package observability

import (
	"fmt"
	"io"
	"math"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

const (
	telemetryPrefix = "SSHCLOUD_TELEMETRY_V1"

	defaultConsoleQueueBytes         = 1 << 20
	defaultConsoleLineBytes          = 16 << 10
	defaultConsoleLinesPerSecond     = 200
	defaultConsoleBytesPerSecond     = 256 << 10
	defaultTelemetryNames            = 32
	defaultTelemetryRecordsPerSecond = 20

	hardConsoleQueueBytes         = 4 << 20
	hardConsoleLineBytes          = 64 << 10
	hardConsoleLinesPerSecond     = 1_000
	hardConsoleBytesPerSecond     = 4 << 20
	hardTelemetryNames            = 64
	hardTelemetryRecordsPerSecond = 100
	consoleChunkBytes             = 32 << 10
)

var telemetryNamePattern = regexp.MustCompile(`^[a-z][a-z0-9_.-]{0,63}$`)

// ConsoleLimits are fixed host controls. Values are clamped to hard maxima.
type ConsoleLimits struct {
	QueueBytes                int
	LineBytes                 int
	LinesPerSecond            int
	BytesPerSecond            int
	TelemetryNames            int
	TelemetryRecordsPerSecond int
}

// ConsoleConfig describes one host-authoritative VMM output drain.
type ConsoleConfig struct {
	Identity RuntimeIdentity
	Sink     *JSONSink
	Metrics  *Registry
	Limits   ConsoleLimits
}

// AppTelemetry is the only guest telemetry schema. Labels, attributes, and
// guest-supplied identity are intentionally unsupported.
type AppTelemetry struct {
	Kind  string
	Name  string
	Value float64
}

// ParseAppTelemetry recognizes the exact four-token line convention:
//
//	SSHCLOUD_TELEMETRY_V1 <counter|gauge> <name> <number>
//
// matched is true whenever the reserved prefix is present, including when the
// remainder is invalid.
func ParseAppTelemetry(line string) (telemetry AppTelemetry, matched bool, err error) {
	if !strings.HasPrefix(line, telemetryPrefix) {
		return AppTelemetry{}, false, nil
	}
	fields := strings.Fields(line)
	if len(fields) != 4 || fields[0] != telemetryPrefix {
		return AppTelemetry{}, true, fmt.Errorf("telemetry must contain exactly four tokens")
	}
	if fields[1] != "counter" && fields[1] != "gauge" {
		return AppTelemetry{}, true, fmt.Errorf("telemetry kind must be counter or gauge")
	}
	if !telemetryNamePattern.MatchString(fields[2]) {
		return AppTelemetry{}, true, fmt.Errorf("invalid telemetry name")
	}
	value, parseErr := strconv.ParseFloat(fields[3], 64)
	if parseErr != nil || math.IsNaN(value) || math.IsInf(value, 0) || math.Abs(value) > 1e15 {
		return AppTelemetry{}, true, fmt.Errorf("invalid telemetry value")
	}
	if fields[1] == "counter" && value < 0 {
		return AppTelemetry{}, true, fmt.Errorf("counter value must be nonnegative")
	}
	return AppTelemetry{Kind: fields[1], Name: fields[2], Value: value}, true, nil
}

type consoleStream uint8

const (
	streamApp consoleStream = iota
	streamDiagnostic
)

type consoleChunk struct {
	stream consoleStream
	data   []byte
}

// ConsoleSink drains Firecracker output through a bounded, nonblocking queue.
// Slow logging backends can drop output but can never backpressure the VMM.
type ConsoleSink struct {
	identity RuntimeIdentity
	sink     *JSONSink
	metrics  *Registry
	limits   ConsoleLimits

	queue      chan consoleChunk
	queueBytes atomic.Int64
	sendMu     sync.Mutex
	closed     bool
	closeOnce  sync.Once
	done       chan struct{}
}

// NewConsoleSink creates one app-console/Firecracker-diagnostic separator.
func NewConsoleSink(config ConsoleConfig) (*ConsoleSink, error) {
	if err := config.Identity.Validate(false); err != nil {
		return nil, err
	}
	if config.Identity.RunID == "" {
		return nil, fmt.Errorf("console identity run id is required")
	}
	if config.Identity.Host == "" {
		return nil, fmt.Errorf("console identity host is required")
	}
	if config.Sink == nil {
		config.Sink = DefaultSink()
	}
	if config.Metrics == nil {
		config.Metrics = DefaultMetrics()
	}
	config.Limits = normalizeConsoleLimits(config.Limits)
	queueItems := config.Limits.QueueBytes/consoleChunkBytes + 2
	sink := &ConsoleSink{
		identity: config.Identity,
		sink:     config.Sink,
		metrics:  config.Metrics,
		limits:   config.Limits,
		queue:    make(chan consoleChunk, queueItems),
		done:     make(chan struct{}),
	}
	go sink.consume()
	return sink, nil
}

func normalizeConsoleLimits(limits ConsoleLimits) ConsoleLimits {
	limits.QueueBytes = boundedLimit(limits.QueueBytes, defaultConsoleQueueBytes, hardConsoleQueueBytes)
	limits.LineBytes = boundedLimit(limits.LineBytes, defaultConsoleLineBytes, hardConsoleLineBytes)
	limits.LinesPerSecond = boundedLimit(limits.LinesPerSecond, defaultConsoleLinesPerSecond, hardConsoleLinesPerSecond)
	limits.BytesPerSecond = boundedLimit(limits.BytesPerSecond, defaultConsoleBytesPerSecond, hardConsoleBytesPerSecond)
	limits.TelemetryNames = boundedLimit(limits.TelemetryNames, defaultTelemetryNames, hardTelemetryNames)
	limits.TelemetryRecordsPerSecond = boundedLimit(
		limits.TelemetryRecordsPerSecond,
		defaultTelemetryRecordsPerSecond,
		hardTelemetryRecordsPerSecond,
	)
	return limits
}

func boundedLimit(value, defaultValue, maximum int) int {
	if value <= 0 {
		return defaultValue
	}
	if value > maximum {
		return maximum
	}
	return value
}

type consoleWriter struct {
	sink   *ConsoleSink
	stream consoleStream
}

// AppWriter receives guest serial-console output.
func (s *ConsoleSink) AppWriter() io.Writer {
	return consoleWriter{sink: s, stream: streamApp}
}

// DiagnosticsWriter receives jailer/Firecracker process diagnostics.
func (s *ConsoleSink) DiagnosticsWriter() io.Writer {
	return consoleWriter{sink: s, stream: streamDiagnostic}
}

func (w consoleWriter) Write(p []byte) (int, error) {
	original := len(p)
	for len(p) > 0 {
		size := min(len(p), consoleChunkBytes)
		size = min(size, w.sink.limits.QueueBytes)
		chunk := append([]byte(nil), p[:size]...)
		w.sink.enqueue(w.stream, chunk)
		p = p[size:]
	}
	return original, nil
}

func (s *ConsoleSink) enqueue(stream consoleStream, data []byte) {
	size := int64(len(data))
	for {
		current := s.queueBytes.Load()
		if current+size > int64(s.limits.QueueBytes) {
			s.drop(stream, len(data))
			return
		}
		if s.queueBytes.CompareAndSwap(current, current+size) {
			break
		}
	}
	s.metrics.AddDiagnosticsQueueBytes(size)

	s.sendMu.Lock()
	if s.closed {
		s.sendMu.Unlock()
		s.queueBytes.Add(-size)
		s.metrics.AddDiagnosticsQueueBytes(-size)
		s.drop(stream, len(data))
		return
	}
	select {
	case s.queue <- consoleChunk{stream: stream, data: data}:
		s.sendMu.Unlock()
	default:
		s.sendMu.Unlock()
		s.queueBytes.Add(-size)
		s.metrics.AddDiagnosticsQueueBytes(-size)
		s.drop(stream, len(data))
	}
}

func (s *ConsoleSink) drop(stream consoleStream, bytes int) {
	kind := "diagnostic"
	if stream == streamApp {
		kind = "log"
		s.metrics.AddAppLogBytes("dropped", bytes)
	}
	s.metrics.AddConsoleRecord(kind, "dropped")
}

// Close asks the emitter to flush, but never waits long enough to block VM
// lifecycle teardown on a stuck logging backend.
func (s *ConsoleSink) Close() {
	s.closeOnce.Do(func() {
		s.sendMu.Lock()
		s.closed = true
		close(s.queue)
		s.sendMu.Unlock()
	})
	select {
	case <-s.done:
	case <-time.After(250 * time.Millisecond):
	}
}

type lineBuffer struct {
	data      []byte
	total     int
	truncated int
}

func (s *ConsoleSink) consume() {
	defer close(s.done)
	states := map[consoleStream]*lineBuffer{
		streamApp:        {},
		streamDiagnostic: {},
	}
	appRate := newFixedRate(s.limits.LinesPerSecond, s.limits.BytesPerSecond)
	diagnosticRate := newFixedRate(s.limits.LinesPerSecond, s.limits.BytesPerSecond)
	telemetryRate := newFixedRate(s.limits.TelemetryRecordsPerSecond, s.limits.BytesPerSecond)
	telemetryNames := make(map[string]string)
	for chunk := range s.queue {
		state := states[chunk.stream]
		for _, value := range chunk.data {
			if value == '\n' {
				s.processLine(chunk.stream, state, appRate, diagnosticRate, telemetryRate, telemetryNames)
				*state = lineBuffer{}
				continue
			}
			state.total++
			if len(state.data) < s.limits.LineBytes {
				state.data = append(state.data, value)
			} else {
				state.truncated++
			}
		}
		s.queueBytes.Add(-int64(len(chunk.data)))
		s.metrics.AddDiagnosticsQueueBytes(-int64(len(chunk.data)))
	}
	for stream, state := range states {
		if state.total > 0 || len(state.data) > 0 {
			s.processLine(stream, state, appRate, diagnosticRate, telemetryRate, telemetryNames)
		}
	}
}

func (s *ConsoleSink) processLine(
	stream consoleStream,
	state *lineBuffer,
	appRate, diagnosticRate, telemetryRate *fixedRate,
	telemetryNames map[string]string,
) {
	message := strings.TrimSuffix(string(state.data), "\r")
	bytes := state.total
	retainedBytes := max(bytes-state.truncated, 0)
	if state.truncated > 0 {
		kind := "diagnostic"
		if stream == streamApp {
			kind = "log"
			s.metrics.AddAppLogBytes("dropped", state.truncated)
		}
		s.metrics.AddConsoleRecord(kind, "truncated")
	}
	if stream == streamDiagnostic {
		if !diagnosticRate.Allow(bytes) {
			s.drop(stream, retainedBytes)
			return
		}
		if err := s.sink.emitDiagnostic(s.identity, message, state.truncated); err != nil {
			s.drop(stream, retainedBytes)
			return
		}
		s.metrics.AddConsoleRecord("diagnostic", "accepted")
		return
	}

	var telemetry AppTelemetry
	var matched bool
	var parseErr error
	if state.truncated == 0 {
		telemetry, matched, parseErr = ParseAppTelemetry(message)
	}
	if matched && parseErr != nil {
		s.metrics.AddConsoleRecord("telemetry", "invalid")
	}
	if parseErr == nil && matched {
		knownKind, known := telemetryNames[telemetry.Name]
		if known && knownKind != telemetry.Kind {
			s.metrics.AddConsoleRecord("telemetry", "invalid")
		} else if (known || len(telemetryNames) < s.limits.TelemetryNames) && telemetryRate.Allow(bytes) {
			telemetryNames[telemetry.Name] = telemetry.Kind
			if err := s.sink.emitAppTelemetry(s.identity, telemetry); err != nil {
				s.metrics.AddAppLogBytes("dropped", retainedBytes)
				s.metrics.AddConsoleRecord("telemetry", "dropped")
				return
			}
			s.metrics.AddAppLogBytes("accepted", retainedBytes)
			s.metrics.AddConsoleRecord("telemetry", "accepted")
			return
		} else {
			s.metrics.AddConsoleRecord("telemetry", "dropped")
		}
	}

	if !appRate.Allow(bytes) {
		s.drop(stream, retainedBytes)
		return
	}
	if err := s.sink.emitAppLog(s.identity, message, state.truncated); err != nil {
		s.drop(stream, retainedBytes)
		return
	}
	s.metrics.AddAppLogBytes("accepted", retainedBytes)
	s.metrics.AddConsoleRecord("log", "accepted")
}

type fixedRate struct {
	mu       sync.Mutex
	window   time.Time
	lines    int
	bytes    int
	maxLines int
	maxBytes int
}

func newFixedRate(maxLines, maxBytes int) *fixedRate {
	return &fixedRate{maxLines: maxLines, maxBytes: maxBytes}
}

func (r *fixedRate) Allow(bytes int) bool {
	r.mu.Lock()
	defer r.mu.Unlock()
	now := time.Now()
	if r.window.IsZero() || now.Sub(r.window) >= time.Second {
		r.window = now
		r.lines = 0
		r.bytes = 0
	}
	if r.lines+1 > r.maxLines || r.bytes+bytes > r.maxBytes {
		return false
	}
	r.lines++
	r.bytes += bytes
	return true
}

type appLogRecord struct {
	Timestamp      time.Time `json:"timestamp"`
	Severity       string    `json:"severity"`
	LogType        string    `json:"log_type"`
	Component      string    `json:"component"`
	User           string    `json:"user"`
	App            string    `json:"app"`
	Generation     string    `json:"generation,omitempty"`
	RunID          string    `json:"run_id"`
	Host           string    `json:"host,omitempty"`
	Stream         string    `json:"stream"`
	Message        string    `json:"message"`
	TruncatedBytes int       `json:"truncated_bytes,omitempty"`
}

func (s *JSONSink) emitAppLog(identity RuntimeIdentity, message string, truncated int) error {
	return s.emit(appLogRecord{
		Timestamp: s.timestamp(), Severity: "INFO", LogType: "app", Component: "app_console",
		User: identity.User, App: identity.App, Generation: identity.Generation,
		RunID: identity.RunID, Host: identity.Host, Stream: "console",
		Message: message, TruncatedBytes: truncated,
	})
}

func (s *JSONSink) emitDiagnostic(identity RuntimeIdentity, message string, truncated int) error {
	return s.emit(appLogRecord{
		Timestamp: s.timestamp(), Severity: "WARNING", LogType: "platform", Component: "firecracker",
		User: identity.User, App: identity.App, Generation: identity.Generation,
		RunID: identity.RunID, Host: identity.Host, Stream: "diagnostic",
		Message: message, TruncatedBytes: truncated,
	})
}

type appTelemetryRecord struct {
	Timestamp  time.Time `json:"timestamp"`
	Severity   string    `json:"severity"`
	LogType    string    `json:"log_type"`
	Component  string    `json:"component"`
	Event      string    `json:"event"`
	User       string    `json:"user"`
	App        string    `json:"app"`
	Generation string    `json:"generation,omitempty"`
	RunID      string    `json:"run_id"`
	Host       string    `json:"host,omitempty"`
	Kind       string    `json:"telemetry_kind"`
	Name       string    `json:"telemetry_name"`
	Value      float64   `json:"telemetry_value"`
}

func (s *JSONSink) emitAppTelemetry(identity RuntimeIdentity, telemetry AppTelemetry) error {
	return s.emit(appTelemetryRecord{
		Timestamp: s.timestamp(), Severity: "INFO", LogType: "app", Component: "app_telemetry",
		Event: "app_telemetry", User: identity.User, App: identity.App,
		Generation: identity.Generation, RunID: identity.RunID, Host: identity.Host,
		Kind: telemetry.Kind, Name: telemetry.Name, Value: telemetry.Value,
	})
}
