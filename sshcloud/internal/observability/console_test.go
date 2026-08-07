package observability

import (
	"bytes"
	"encoding/json"
	"io"
	"reflect"
	"strings"
	"sync"
	"testing"
	"time"
)

func testRuntimeIdentity() RuntimeIdentity {
	return RuntimeIdentity{
		User: "alice", App: "fortune", Generation: "g123",
		RunID: "r0123456789abcdef0123456789abcdef", Host: "agent-1",
	}
}

func TestAppTelemetryValidation(t *testing.T) {
	t.Parallel()
	tests := []struct {
		line    string
		matched bool
		valid   bool
	}{
		{"ordinary app output", false, true},
		{"SSHCLOUD_TELEMETRY_V1 counter requests_total 3", true, true},
		{"SSHCLOUD_TELEMETRY_V1 gauge queue.depth -2.5", true, true},
		{"SSHCLOUD_TELEMETRY_V1 histogram latency 1", true, false},
		{"SSHCLOUD_TELEMETRY_V1 counter BadName 1", true, false},
		{"SSHCLOUD_TELEMETRY_V1 counter requests_total -1", true, false},
		{"SSHCLOUD_TELEMETRY_V1 gauge value NaN", true, false},
		{"SSHCLOUD_TELEMETRY_V1 gauge value 1 label=x", true, false},
	}
	for _, test := range tests {
		_, matched, err := ParseAppTelemetry(test.line)
		if matched != test.matched {
			t.Errorf("%q matched = %v, want %v", test.line, matched, test.matched)
		}
		if (err == nil) != test.valid {
			t.Errorf("%q error = %v, valid = %v", test.line, err, test.valid)
		}
	}
}

func TestConsoleDoesNotPromoteGuestJSONFields(t *testing.T) {
	t.Parallel()
	var output bytes.Buffer
	console, err := NewConsoleSink(ConsoleConfig{
		Identity: testRuntimeIdentity(),
		Sink:     NewJSONSink(&output, "vmmhelper"),
		Metrics:  NewRegistry(),
	})
	if err != nil {
		t.Fatal(err)
	}
	guest := `{"severity":"EMERGENCY","user":"mallory","log_type":"platform"}`
	_, _ = io.WriteString(console.AppWriter(), guest+"\n")
	console.Close()

	var record map[string]any
	if err := json.Unmarshal(bytes.TrimSpace(output.Bytes()), &record); err != nil {
		t.Fatal(err)
	}
	if got := record["message"]; got != guest {
		t.Fatalf("message = %#v, want opaque guest JSON", got)
	}
	if got := record["user"]; got != "alice" {
		t.Fatalf("authoritative user = %#v", got)
	}
	if got := record["severity"]; got != "INFO" {
		t.Fatalf("guest promoted severity: %#v", got)
	}
	if got := record["log_type"]; got != "app" {
		t.Fatalf("guest promoted log type: %#v", got)
	}
}

func TestTelemetryCardinalityIsBounded(t *testing.T) {
	t.Parallel()
	var output bytes.Buffer
	metrics := NewRegistry()
	console, err := NewConsoleSink(ConsoleConfig{
		Identity: testRuntimeIdentity(),
		Sink:     NewJSONSink(&output, "vmmhelper"),
		Metrics:  metrics,
		Limits: ConsoleLimits{
			TelemetryNames: 2, TelemetryRecordsPerSecond: 10,
			LinesPerSecond: 10, BytesPerSecond: 1 << 20,
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"first", "second", "third"} {
		_, _ = io.WriteString(console.AppWriter(), "SSHCLOUD_TELEMETRY_V1 counter "+name+" 1\n")
	}
	console.Close()

	decoder := json.NewDecoder(bytes.NewReader(output.Bytes()))
	var telemetryRecords, logRecords int
	for {
		var record map[string]any
		if err := decoder.Decode(&record); err == io.EOF {
			break
		} else if err != nil {
			t.Fatal(err)
		}
		switch record["event"] {
		case "app_telemetry":
			telemetryRecords++
		default:
			logRecords++
		}
	}
	if telemetryRecords != 2 || logRecords != 1 {
		t.Fatalf("telemetry/log records = %d/%d, want 2/1", telemetryRecords, logRecords)
	}
	if got := metrics.Value(
		"sshcloud_console_records_total", "kind", "telemetry", "result", "dropped",
	); got != 1 {
		t.Fatalf("telemetry dropped metric = %v, want 1", got)
	}
}

func TestTelemetryNameCannotChangeKindWithinRun(t *testing.T) {
	t.Parallel()
	var output bytes.Buffer
	metrics := NewRegistry()
	console, err := NewConsoleSink(ConsoleConfig{
		Identity: testRuntimeIdentity(),
		Sink:     NewJSONSink(&output, "vmmhelper"),
		Metrics:  metrics,
	})
	if err != nil {
		t.Fatal(err)
	}
	_, _ = io.WriteString(console.AppWriter(), "SSHCLOUD_TELEMETRY_V1 counter requests 1\n")
	_, _ = io.WriteString(console.AppWriter(), "SSHCLOUD_TELEMETRY_V1 gauge requests 1\n")
	console.Close()

	if got := strings.Count(output.String(), `"event":"app_telemetry"`); got != 1 {
		t.Fatalf("promoted telemetry records = %d, want 1", got)
	}
	if got := metrics.Value(
		"sshcloud_console_records_total", "kind", "telemetry", "result", "invalid",
	); got != 1 {
		t.Fatalf("invalid telemetry metric = %v, want 1", got)
	}
}

type gatedWriter struct {
	started chan struct{}
	release chan struct{}
	once    sync.Once
}

func (w *gatedWriter) Write(p []byte) (int, error) {
	w.once.Do(func() { close(w.started) })
	<-w.release
	return len(p), nil
}

func TestLogFloodNeverBlocksVMMWriter(t *testing.T) {
	t.Parallel()
	output := &gatedWriter{started: make(chan struct{}), release: make(chan struct{})}
	metrics := NewRegistry()
	console, err := NewConsoleSink(ConsoleConfig{
		Identity: testRuntimeIdentity(),
		Sink:     NewJSONSink(output, "vmmhelper"),
		Metrics:  metrics,
		Limits: ConsoleLimits{
			QueueBytes: 1 << 10, LineBytes: 256,
			LinesPerSecond: 1, BytesPerSecond: 256,
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	writer := console.AppWriter()
	_, _ = io.WriteString(writer, "first\n")
	select {
	case <-output.started:
	case <-time.After(time.Second):
		t.Fatal("console consumer did not reach gated output")
	}

	done := make(chan struct{})
	go func() {
		_, _ = writer.Write(bytes.Repeat([]byte("flood\n"), 1<<20))
		close(done)
	}()
	select {
	case <-done:
	case <-time.After(250 * time.Millisecond):
		t.Fatal("VMM writer blocked behind logging output")
	}
	if got := metrics.Value("sshcloud_app_log_bytes_total", "result", "dropped"); got == 0 {
		t.Fatal("flood did not increment dropped-byte metric")
	}
	close(output.release)
	console.Close()
}

func TestMetadataEventSchemasCannotCarrySSHChannelPayloads(t *testing.T) {
	t.Parallel()
	forbidden := []string{"stdin", "stdout", "stderr", "command", "environment", "signal", "payload", "replay"}
	types := []reflect.Type{
		reflect.TypeOf(LifecycleEvent{}),
		reflect.TypeOf(SessionEvent{}),
		reflect.TypeOf(DeployEvent{}),
		reflect.TypeOf(SnapshotEvent{}),
		reflect.TypeOf(MigrationEvent{}),
	}
	for _, eventType := range types {
		for index := 0; index < eventType.NumField(); index++ {
			field := strings.ToLower(eventType.Field(index).Name)
			for _, token := range forbidden {
				if strings.Contains(field, token) {
					t.Fatalf("%s exposes forbidden field %s", eventType, eventType.Field(index).Name)
				}
			}
		}
	}

	sentinels := []string{
		"SSH_STDIN_SENTINEL", "SSH_STDOUT_SENTINEL", "SSH_STDERR_SENTINEL",
		"SSH_COMMAND_SENTINEL", "SSH_ENV_SENTINEL", "SSH_SIGNAL_SENTINEL",
	}
	var output bytes.Buffer
	sink := NewJSONSink(&output, "gateway")
	if err := sink.Emit(SessionEvent{
		Identity: RuntimeIdentity{User: "alice", App: "fortune", Generation: "g123"},
		Action:   "end", Route: "app", Mode: "exec", Outcome: OutcomeSuccess,
	}); err != nil {
		t.Fatal(err)
	}
	for _, sentinel := range sentinels {
		if strings.Contains(output.String(), sentinel) {
			t.Fatalf("metadata event contained SSH payload sentinel %q", sentinel)
		}
	}
}
