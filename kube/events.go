package kube

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"regexp"
	"strings"
	"sync/atomic"
	"time"
	"unicode/utf8"

	"github.com/imjasonh/playground/kube/internal/client"
)

// Event types.
const (
	Normal  = "Normal"
	Warning = "Warning"
)

// Event is an event that a reconcile recorded with Eventf.
type Event struct {
	// Type is Normal or Warning.
	Type string
	// Reason is a CamelCase word for what happened, such as Created.
	Reason string
	// Note describes what happened, for people to read.
	Note string
}

// Eventf records an event about the object being reconciled, which people
// see in kubectl describe and kubectl get events. eventType is Normal or
// Warning, reason is a CamelCase word such as Created or Rejected, and the
// note is format and args as fmt.Sprintf formats them, cut to 1,024 bytes.
//
// After Reconcile or Finalize returns, even with an error, the framework
// writes the events as events.k8s.io/v1 Events in the object's namespace,
// or in default for a cluster-scoped object. An event with the same type,
// reason, and note as one about the same object less than 6 minutes earlier
// is a repeat, which adds to the earlier Event's count instead of creating
// another Event. The framework writes events in the background and drops
// them if it falls behind, so recording an event never fails or delays a
// reconcile.
//
// Record an event when something happens, such as a push to a system outside
// Kubernetes, rather than on every reconcile. Once a call such as Get has
// failed the reconcile, Eventf does nothing, because what the reconcile saw
// is incomplete.
func Eventf(ctx context.Context, eventType, reason, format string, args ...any) {
	s := scopeFrom(ctx, "Eventf")
	if s.readOnly("Eventf") || s.err != nil {
		return
	}
	note := truncateNote(fmt.Sprintf(format, args...))
	s.events = append(s.events, eventIntent{Event: Event{Type: eventType, Reason: reason, Note: note}, at: time.Now()})
}

type eventIntent struct {
	Event
	at time.Time
}

// maxNote is the most bytes that the API server accepts in a note.
const maxNote = 1024

func truncateNote(s string) string {
	if len(s) <= maxNote {
		return s
	}
	n := maxNote - len("...")
	for n > 0 && !utf8.RuneStart(s[n]) {
		n--
	}
	return s[:n] + "..."
}

// eventRef is an Event's regarding field. It leaves out the object's
// resource version, because the repeats in one Event can be about different
// versions. The status that the framework writes after a reconcile changes
// the version that the next reconcile sees.
type eventRef struct {
	APIVersion string `json:"apiVersion"`
	Kind       string `json:"kind"`
	Namespace  string `json:"namespace,omitempty"`
	Name       string `json:"name"`
	UID        string `json:"uid,omitempty"`
}

// eventKey identifies repeats of an event.
type eventKey struct {
	controller, action, typ, reason, note string
	regarding                             eventRef
}

type eventRecord struct {
	eventKey
	at time.Time
}

// eventSeries is an Event and its repeats.
type eventSeries struct {
	name, namespace string
	first, last     time.Time
	// count is how many times the event happened, and written is the count
	// that the API server has, or 0 before the Event is created.
	count, written int
	// failed is set when the API server rejected the Event, so the writer
	// doesn't send its repeats.
	failed bool
}

// eventWriter writes the events that reconciles record. Only the goroutine
// that start runs touches series and last.
type eventWriter struct {
	client  *client.Client
	log     *slog.Logger
	metrics *metrics
	host    string
	queue   chan eventRecord
	// finish is how long a series lasts after its last repeat, and how often
	// the writer writes the counts of series and forgets finished ones.
	finish  time.Duration
	series  map[eventKey]*eventSeries
	last    int64
	dropped atomic.Int64
}

func newEventWriter(c *client.Client, log *slog.Logger, m *metrics) *eventWriter {
	host, _ := os.Hostname()
	return &eventWriter{
		client: c, log: log, metrics: m, host: host,
		queue:  make(chan eventRecord, 1000),
		finish: 6 * time.Minute,
		series: map[eventKey]*eventSeries{},
	}
}

// send queues the events that a reconcile of obj recorded in s. It never
// blocks: when the queue is full, it drops the events.
func (w *eventWriter) send(c *core, obj *ObjectMeta, action string, s *scope) {
	if w == nil || len(s.events) == 0 {
		return
	}
	ref := eventRef{APIVersion: c.ti.apiVersion, Kind: c.ti.kind, Namespace: obj.Namespace, Name: obj.Name, UID: obj.UID}
	for _, e := range s.events {
		r := eventRecord{eventKey: eventKey{controller: c.name, action: action, typ: e.Type, reason: e.Reason, note: e.Note, regarding: ref}, at: e.at}
		select {
		case w.queue <- r:
		default:
			w.dropped.Add(1)
			w.metrics.inc("kube_events_total", "controller", c.name, "result", "dropped")
		}
	}
}

// start writes queued events until the returned function is called. That
// function cancels any write in progress, spends at most 5 seconds writing
// the events still queued and the counts of series, then returns.
func (w *eventWriter) start() func() {
	ctx, cancel := context.WithCancel(context.Background())
	done := make(chan struct{})
	go func() {
		defer close(done)
		t := time.NewTicker(w.finish)
		defer t.Stop()
		for ctx.Err() == nil {
			select {
			case r := <-w.queue:
				w.record(ctx, r)
			case now := <-t.C:
				w.flush(ctx, now)
			case <-ctx.Done():
			}
		}
		drain, cancelDrain := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancelDrain()
		for len(w.queue) > 0 && drain.Err() == nil {
			w.record(drain, <-w.queue)
		}
		w.flush(drain, time.Now())
	}()
	return func() {
		cancel()
		<-done
	}
}

// record adds r to its series, or starts a new one when the last repeat was
// w.finish or more earlier. Like client-go's recorder, it creates the Event
// the first time and writes the count right away the second time; flush
// writes later counts.
func (w *eventWriter) record(ctx context.Context, r eventRecord) {
	s := w.series[r.eventKey]
	if s != nil && r.at.Sub(s.last) >= w.finish {
		if s.written != s.count && !s.failed {
			w.write(ctx, r.eventKey, s)
		}
		s = nil
	}
	if s == nil {
		ns := r.regarding.Namespace
		if ns == "" {
			ns = "default"
		}
		s = &eventSeries{name: w.name(r.regarding, r.at), namespace: ns, first: r.at}
		w.series[r.eventKey] = s
	}
	s.count++
	if r.at.After(s.last) {
		s.last = r.at
	}
	if s.count <= 2 && !s.failed {
		w.write(ctx, r.eventKey, s)
	}
}

// flush writes the counts that changed since the last write, and forgets
// series that ended because their last repeat was w.finish or more earlier.
// Once ctx is done, it forgets nothing, so that the writer can still write
// the counts when it stops.
func (w *eventWriter) flush(ctx context.Context, now time.Time) {
	for k, s := range w.series {
		if s.written != s.count && !s.failed && ctx.Err() == nil {
			w.write(ctx, k, s)
		}
		if now.Sub(s.last) >= w.finish && ctx.Err() == nil {
			delete(w.series, k)
		}
	}
	if n := w.dropped.Swap(0); n > 0 {
		w.log.Warn("dropped events because writing them fell behind", "events", n)
	}
}

func (w *eventWriter) write(ctx context.Context, k eventKey, s *eventSeries) {
	created, err := w.put(ctx, k, s)
	if err != nil && errors.Is(ctx.Err(), context.Canceled) {
		// Only stopping the writer cancels ctx, which is no reason to log a
		// failure or to stop writing the series.
		return
	}
	if err != nil {
		w.metrics.inc("kube_events_total", "controller", k.controller, "result", "failed")
		w.log.Warn("writing event failed", "controller", k.controller, "object", k.regarding.Kind+" "+Key{Namespace: k.regarding.Namespace, Name: k.regarding.Name}.String(), "reason", k.reason, "err", err)
		var e *client.APIError
		s.failed = errors.As(err, &e) && e.Code != http.StatusTooManyRequests && e.Code < http.StatusInternalServerError
		return
	}
	s.written = s.count
	result := "updated"
	if created {
		result = "created"
	}
	w.metrics.inc("kube_events_total", "controller", k.controller, "result", result)
}

// put creates the series' Event, or patches its count. It creates the Event
// again if it's gone, as when someone deleted it.
func (w *eventWriter) put(ctx context.Context, k eventKey, s *eventSeries) (created bool, err error) {
	path := client.Path("events.k8s.io/v1", "events", s.namespace, s.name)
	patch, _ := json.Marshal(map[string]any{"series": w.seriesOf(s)})
	if s.written > 0 {
		if err := w.client.Patch(ctx, path, client.MergePatch, nil, patch, nil); !client.IsNotFound(err) {
			return false, err
		}
	}
	err = w.client.Create(ctx, client.Path("events.k8s.io/v1", "events", s.namespace, ""), w.body(k, s), nil)
	if client.IsAlreadyExists(err) {
		// An earlier create succeeded without the writer hearing back.
		if s.count < 2 {
			return true, nil
		}
		return false, w.client.Patch(ctx, path, client.MergePatch, nil, patch, nil)
	}
	return err == nil, err
}

type eventBody struct {
	TypeMeta
	Metadata            ObjectMeta       `json:"metadata"`
	EventTime           string           `json:"eventTime"`
	Series              *eventSeriesBody `json:"series,omitempty"`
	ReportingController string           `json:"reportingController"`
	ReportingInstance   string           `json:"reportingInstance"`
	Action              string           `json:"action"`
	Reason              string           `json:"reason"`
	Regarding           eventRef         `json:"regarding"`
	Note                string           `json:"note,omitempty"`
	Type                string           `json:"type"`
}

type eventSeriesBody struct {
	Count            int    `json:"count"`
	LastObservedTime string `json:"lastObservedTime"`
}

func (w *eventWriter) body(k eventKey, s *eventSeries) eventBody {
	instance := k.controller
	if w.host != "" {
		instance += "-" + w.host
	}
	return eventBody{
		TypeMeta:            TypeMeta{APIVersion: "events.k8s.io/v1", Kind: "Event"},
		Metadata:            ObjectMeta{Name: s.name, Namespace: s.namespace},
		EventTime:           s.first.UTC().Format(microTime),
		Series:              w.seriesOf(s),
		ReportingController: k.controller,
		ReportingInstance:   instance[:min(len(instance), 128)],
		Action:              k.action,
		Reason:              k.reason,
		Regarding:           k.regarding,
		Note:                k.note,
		Type:                k.typ,
	}
}

func (w *eventWriter) seriesOf(s *eventSeries) *eventSeriesBody {
	if s.count < 2 {
		return nil
	}
	return &eventSeriesBody{Count: s.count, LastObservedTime: s.last.UTC().Format(microTime)}
}

var dnsSubdomain = regexp.MustCompile(`^[a-z0-9]([-a-z0-9]*[a-z0-9])?(\.[a-z0-9]([-a-z0-9]*[a-z0-9])?)*$`)

// name returns a new Event's name: the object's name and a hexadecimal
// timestamp, as client-go names them. Each name's timestamp is later than the
// last, so two events in the same nanosecond get different names.
func (w *eventWriter) name(ref eventRef, at time.Time) string {
	w.last = max(at.UnixNano(), w.last+1)
	prefix := ref.Name
	if len(prefix) > 236 || !dnsSubdomain.MatchString(prefix) {
		prefix = strings.ToLower(ref.Kind)
	}
	return fmt.Sprintf("%s.%x", prefix, w.last)
}
