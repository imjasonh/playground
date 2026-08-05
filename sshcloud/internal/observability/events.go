package observability

import (
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"regexp"
	"strings"
	"time"

	"github.com/imjasonh/playground/sshcloud/internal/genid"
	"github.com/imjasonh/playground/sshcloud/internal/names"
)

var (
	runIDPattern = regexp.MustCompile(`^r[0-9a-f]{32}$`)
	hostPattern  = regexp.MustCompile(`^[A-Za-z0-9][A-Za-z0-9._-]{0,62}$`)
)

// RuntimeIdentity is authoritative host metadata. Guests cannot provide or
// override any of these fields.
type RuntimeIdentity struct {
	User       string `json:"user,omitempty"`
	App        string `json:"app,omitempty"`
	Generation string `json:"generation,omitempty"`
	RunID      string `json:"run_id,omitempty"`
	Host       string `json:"host,omitempty"`
}

// Validate checks the bounded identity syntax shared by logs and events.
func (i RuntimeIdentity) Validate(allowEmpty bool) error {
	if !allowEmpty && (i.User == "" || i.App == "") {
		return fmt.Errorf("user and app are required")
	}
	if i.User != "" {
		if err := names.ValidateIdent(i.User); err != nil {
			return fmt.Errorf("user: %w", err)
		}
	}
	if i.App != "" {
		if err := names.ValidateIdent(i.App); err != nil {
			return fmt.Errorf("app: %w", err)
		}
	}
	if i.Generation != "" {
		if err := genid.Validate(i.Generation); err != nil {
			return err
		}
	}
	if i.RunID != "" && !runIDPattern.MatchString(i.RunID) {
		return fmt.Errorf("invalid run id")
	}
	if i.Host != "" && !hostPattern.MatchString(i.Host) {
		return fmt.Errorf("invalid host id")
	}
	return nil
}

// NewRunID returns a non-guest-selectable identifier for one VMM run.
func NewRunID() string {
	var value [16]byte
	if _, err := rand.Read(value[:]); err == nil {
		return "r" + hex.EncodeToString(value[:])
	}
	return fmt.Sprintf("r%032x", time.Now().UnixNano())
}

// Outcome is deliberately low-cardinality.
type Outcome string

const (
	OutcomeSuccess  Outcome = "success"
	OutcomeFailure  Outcome = "failure"
	OutcomeRejected Outcome = "rejected"
	OutcomeTimeout  Outcome = "timeout"
)

func (o Outcome) valid() bool {
	switch o {
	case OutcomeSuccess, OutcomeFailure, OutcomeRejected, OutcomeTimeout:
		return true
	default:
		return false
	}
}

// Event is sealed so callers can emit only the metadata-only event schemas in
// this package. There is intentionally no free-form payload or error field.
type Event interface {
	privacySafeEvent()
	toRecord(*JSONSink) (eventRecord, error)
	metric() (family, operation string, outcome Outcome, duration time.Duration)
}

// LifecycleEvent describes a host-side instance transition.
type LifecycleEvent struct {
	Identity  RuntimeIdentity
	Operation string
	State     string
	Outcome   Outcome
	Duration  time.Duration
}

func (LifecycleEvent) privacySafeEvent() {}

func (e LifecycleEvent) toRecord(s *JSONSink) (eventRecord, error) {
	if !oneOf(e.Operation, "boot", "restore", "sleep", "wake", "evict", "stop", "cordon", "uncordon") {
		return eventRecord{}, fmt.Errorf("invalid lifecycle operation")
	}
	hostOperation := e.Operation == "cordon" || e.Operation == "uncordon"
	if err := e.Identity.Validate(hostOperation); err != nil {
		return eventRecord{}, err
	}
	if e.State != "" && !oneOf(e.State, "running", "sleeping", "stopped", "failed", "cordoned", "uncordoned") {
		return eventRecord{}, fmt.Errorf("invalid lifecycle state")
	}
	return newEventRecord(s, "lifecycle", e.Identity, e.Operation, e.Outcome, e.Duration), validateOutcome(e.Outcome)
}

func (e LifecycleEvent) metric() (string, string, Outcome, time.Duration) {
	return "lifecycle", e.Operation, e.Outcome, e.Duration
}

// SessionEvent records routing and lifecycle metadata only. It has no SSH
// command, environment, signal, channel byte, or replay field.
type SessionEvent struct {
	Identity RuntimeIdentity
	Action   string
	Route    string
	Mode     string
	Outcome  Outcome
	Duration time.Duration
}

func (SessionEvent) privacySafeEvent() {}

func (e SessionEvent) toRecord(s *JSONSink) (eventRecord, error) {
	if err := e.Identity.Validate(true); err != nil {
		return eventRecord{}, err
	}
	if !oneOf(e.Action, "admit", "start", "end", "freeze", "thaw", "abort") {
		return eventRecord{}, fmt.Errorf("invalid session action")
	}
	if e.Route != "" && !oneOf(e.Route, "join", "menu", "deploy", "app", "busy", "forbidden") {
		return eventRecord{}, fmt.Errorf("invalid session route")
	}
	if e.Mode != "" && !oneOf(e.Mode, "shell", "exec", "subsystem") {
		return eventRecord{}, fmt.Errorf("invalid session mode")
	}
	record := newEventRecord(s, "session", e.Identity, e.Action, e.Outcome, e.Duration)
	record.Route = e.Route
	record.Mode = e.Mode
	return record, validateOutcome(e.Outcome)
}

func (e SessionEvent) metric() (string, string, Outcome, time.Duration) {
	return "session", e.Action, e.Outcome, e.Duration
}

// DeployEvent describes a deploy state transition without recording an image
// reference or the SSH command that requested it.
type DeployEvent struct {
	Identity RuntimeIdentity
	Action   string
	Strategy string
	Tier     string
	Outcome  Outcome
	Duration time.Duration
}

func (DeployEvent) privacySafeEvent() {}

func (e DeployEvent) toRecord(s *JSONSink) (eventRecord, error) {
	if err := e.Identity.Validate(false); err != nil {
		return eventRecord{}, err
	}
	if !oneOf(e.Action, "deploy", "reconcile", "drain", "retire") {
		return eventRecord{}, fmt.Errorf("invalid deploy action")
	}
	if e.Strategy != "" && !oneOf(e.Strategy, "drain", "kick") {
		return eventRecord{}, fmt.Errorf("invalid deploy strategy")
	}
	if e.Tier != "" && !oneOf(e.Tier, "tiny", "small") {
		return eventRecord{}, fmt.Errorf("invalid deploy tier")
	}
	record := newEventRecord(s, "deploy", e.Identity, e.Action, e.Outcome, e.Duration)
	record.Strategy = e.Strategy
	record.Tier = e.Tier
	return record, validateOutcome(e.Outcome)
}

func (e DeployEvent) metric() (string, string, Outcome, time.Duration) {
	return "deploy", e.Action, e.Outcome, e.Duration
}

// SnapshotEvent describes a fixed snapshot package operation.
type SnapshotEvent struct {
	Identity RuntimeIdentity
	Action   string
	Outcome  Outcome
	Duration time.Duration
}

func (SnapshotEvent) privacySafeEvent() {}

func (e SnapshotEvent) toRecord(s *JSONSink) (eventRecord, error) {
	if err := e.Identity.Validate(false); err != nil {
		return eventRecord{}, err
	}
	if !oneOf(e.Action, "put", "get", "has", "meta", "delete", "create", "load") {
		return eventRecord{}, fmt.Errorf("invalid snapshot action")
	}
	return newEventRecord(s, "snapshot", e.Identity, e.Action, e.Outcome, e.Duration), validateOutcome(e.Outcome)
}

func (e SnapshotEvent) metric() (string, string, Outcome, time.Duration) {
	return "snapshot", e.Action, e.Outcome, e.Duration
}

// MigrationEvent describes control-plane phases. The bounded in-memory
// migration input buffer is intentionally absent and is never observable.
type MigrationEvent struct {
	Identity RuntimeIdentity
	Action   string
	FromHost string
	ToHost   string
	Outcome  Outcome
	Duration time.Duration
}

func (MigrationEvent) privacySafeEvent() {}

func (e MigrationEvent) toRecord(s *JSONSink) (eventRecord, error) {
	if err := e.Identity.Validate(false); err != nil {
		return eventRecord{}, err
	}
	if !oneOf(e.Action, "migrate", "freeze", "thaw", "drain") {
		return eventRecord{}, fmt.Errorf("invalid migration action")
	}
	for _, host := range []string{e.FromHost, e.ToHost} {
		if host != "" && !hostPattern.MatchString(host) {
			return eventRecord{}, fmt.Errorf("invalid migration host")
		}
	}
	record := newEventRecord(s, "migration", e.Identity, e.Action, e.Outcome, e.Duration)
	record.FromHost = e.FromHost
	record.ToHost = e.ToHost
	return record, validateOutcome(e.Outcome)
}

func (e MigrationEvent) metric() (string, string, Outcome, time.Duration) {
	return "migration", e.Action, e.Outcome, e.Duration
}

type eventRecord struct {
	Timestamp  time.Time `json:"timestamp"`
	Severity   string    `json:"severity"`
	LogType    string    `json:"log_type"`
	Component  string    `json:"component"`
	Event      string    `json:"event"`
	User       string    `json:"user,omitempty"`
	App        string    `json:"app,omitempty"`
	Generation string    `json:"generation,omitempty"`
	RunID      string    `json:"run_id,omitempty"`
	Host       string    `json:"host,omitempty"`
	Action     string    `json:"action"`
	Outcome    Outcome   `json:"outcome"`
	Route      string    `json:"route,omitempty"`
	Mode       string    `json:"mode,omitempty"`
	Strategy   string    `json:"strategy,omitempty"`
	Tier       string    `json:"tier,omitempty"`
	FromHost   string    `json:"from_host,omitempty"`
	ToHost     string    `json:"to_host,omitempty"`
	DurationMS int64     `json:"duration_ms,omitempty"`
}

func newEventRecord(s *JSONSink, event string, identity RuntimeIdentity, action string, outcome Outcome, duration time.Duration) eventRecord {
	severity := "INFO"
	if outcome == OutcomeFailure {
		severity = "ERROR"
	} else if outcome == OutcomeTimeout {
		severity = "WARNING"
	}
	durationMS := duration.Milliseconds()
	if durationMS < 0 {
		durationMS = 0
	}
	return eventRecord{
		Timestamp: s.timestamp(), Severity: severity, LogType: "platform",
		Component: s.componentName(), Event: event,
		User: identity.User, App: identity.App, Generation: identity.Generation,
		RunID: identity.RunID, Host: identity.Host,
		Action: action, Outcome: outcome, DurationMS: durationMS,
	}
}

func validateOutcome(outcome Outcome) error {
	if !outcome.valid() {
		return fmt.Errorf("invalid event outcome")
	}
	return nil
}

func oneOf(value string, allowed ...string) bool {
	for _, candidate := range allowed {
		if value == candidate {
			return true
		}
	}
	return false
}

// Emit writes one validated metadata-only event and updates aggregate metrics.
func (s *JSONSink) Emit(event Event) error {
	if event == nil {
		return fmt.Errorf("event is nil")
	}
	record, err := event.toRecord(s)
	if err != nil {
		return err
	}
	family, operation, outcome, duration := event.metric()
	DefaultMetrics().ObserveOperation(family, operation, string(outcome), duration)
	return s.emit(record)
}

// Emit writes through the process-wide sink. Invalid metadata is dropped
// rather than falling back to an unsafe free-form event.
func Emit(event Event) {
	_ = defaultSink.Emit(event)
}

func routeForAction(action string) string {
	action = strings.TrimSpace(action)
	switch action {
	case "join", "menu", "deploy":
		return action
	case "proxy_app":
		return "app"
	case "reject_busy":
		return "busy"
	case "forbidden":
		return "forbidden"
	default:
		return ""
	}
}

// SessionRoute converts the gateway's fixed action name to an event route.
func SessionRoute(action string) string { return routeForAction(action) }
