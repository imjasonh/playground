// Package observability provides the privacy boundary for platform logs,
// metadata-only events, app console output, and aggregate metrics.
package observability

import (
	"encoding/json"
	"io"
	"log"
	"os"
	"strings"
	"sync"
	"time"
	"unicode/utf8"
)

const maxPlatformMessageBytes = 8 << 10

// JSONSink serializes records to one JSON object per line. It never attempts
// to parse a message as JSON, so untrusted guest fields cannot become trusted
// Cloud Logging fields.
type JSONSink struct {
	mu        sync.Mutex
	output    io.Writer
	component string
	now       func() time.Time
}

// NewJSONSink returns a concurrency-safe JSON-lines sink.
func NewJSONSink(output io.Writer, component string) *JSONSink {
	if output == nil {
		output = io.Discard
	}
	return &JSONSink{
		output:    output,
		component: normalizeComponent(component),
		now:       time.Now,
	}
}

var defaultSink = NewJSONSink(os.Stderr, "sshcloud")

// DefaultSink is the process-wide sink used by platform binaries.
func DefaultSink() *JSONSink { return defaultSink }

// Configure converts the standard library logger to structured JSON without
// requiring every existing log.Printf call to be rewritten.
func Configure(component string) {
	defaultSink.setComponent(component)
	log.SetFlags(0)
	log.SetPrefix("")
	log.SetOutput(legacyLogWriter{sink: defaultSink})
}

func (s *JSONSink) setComponent(component string) {
	s.mu.Lock()
	s.component = normalizeComponent(component)
	s.mu.Unlock()
}

func normalizeComponent(component string) string {
	component = strings.TrimSpace(component)
	if component == "" {
		return "sshcloud"
	}
	return component
}

func (s *JSONSink) timestamp() time.Time {
	s.mu.Lock()
	now := s.now
	s.mu.Unlock()
	return now().UTC()
}

func (s *JSONSink) componentName() string {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.component
}

func (s *JSONSink) emit(record any) error {
	encoded, err := json.Marshal(record)
	if err != nil {
		return err
	}
	encoded = append(encoded, '\n')
	s.mu.Lock()
	defer s.mu.Unlock()
	_, err = s.output.Write(encoded)
	return err
}

type platformLogRecord struct {
	Timestamp      time.Time `json:"timestamp"`
	Severity       string    `json:"severity"`
	LogType        string    `json:"log_type"`
	Component      string    `json:"component"`
	Message        string    `json:"message"`
	TruncatedBytes int       `json:"truncated_bytes,omitempty"`
}

// PlatformMessage emits one opaque, bounded platform message.
func (s *JSONSink) PlatformMessage(severity, message string) error {
	message, truncated := truncateUTF8(message, maxPlatformMessageBytes)
	return s.emit(platformLogRecord{
		Timestamp:      s.timestamp(),
		Severity:       normalizeSeverity(severity),
		LogType:        "platform",
		Component:      s.componentName(),
		Message:        message,
		TruncatedBytes: truncated,
	})
}

func normalizeSeverity(severity string) string {
	switch strings.ToUpper(strings.TrimSpace(severity)) {
	case "DEBUG", "INFO", "NOTICE", "WARNING", "ERROR", "CRITICAL", "ALERT", "EMERGENCY":
		return strings.ToUpper(strings.TrimSpace(severity))
	default:
		return "INFO"
	}
}

func truncateUTF8(value string, limit int) (string, int) {
	if limit <= 0 || len(value) <= limit {
		return value, 0
	}
	end := limit
	for end > 0 && !utf8.ValidString(value[:end]) {
		end--
	}
	if end == 0 {
		end = limit
	}
	return value[:end], len(value) - end
}

type legacyLogWriter struct {
	sink *JSONSink
}

func (w legacyLogWriter) Write(p []byte) (int, error) {
	original := len(p)
	text := strings.TrimRight(string(p), "\r\n")
	if text == "" {
		return original, nil
	}
	severity := "INFO"
	upper := strings.ToUpper(text)
	switch {
	case strings.HasPrefix(upper, "WARNING:"):
		severity = "WARNING"
	case strings.HasPrefix(upper, "ERROR:"):
		severity = "ERROR"
	}
	for _, line := range strings.Split(text, "\n") {
		if err := w.sink.PlatformMessage(severity, strings.TrimSuffix(line, "\r")); err != nil {
			return original, err
		}
	}
	return original, nil
}
