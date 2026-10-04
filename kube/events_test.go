package kube

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"log/slog"
	"maps"
	"net/http"
	"net/http/httptest"
	"reflect"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"
	"unicode/utf8"

	"github.com/imjasonh/playground/kube/internal/client"
)

// eventServer is an API server that stores Events.
type eventServer struct {
	mu     sync.Mutex
	events map[string]map[string]any
	reqs   []string
	// fail is the status code of every response when it's set.
	fail int
	// lose makes the server store the Events it's sent but answer 500, as
	// when a response is lost.
	lose bool
}

func (s *eventServer) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.reqs = append(s.reqs, r.Method+" "+r.URL.Path)
	reply := func(code int, reason string) {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(code)
		_ = json.NewEncoder(w).Encode(map[string]any{"kind": "Status", "code": code, "reason": reason})
	}
	if s.fail != 0 {
		reply(s.fail, "")
		return
	}
	var body map[string]any
	if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
		reply(http.StatusBadRequest, "BadRequest")
		return
	}
	switch r.Method {
	case http.MethodPost:
		meta, _ := body["metadata"].(map[string]any)
		path := r.URL.Path + "/" + fmt.Sprint(meta["name"])
		if _, ok := s.events[path]; ok {
			reply(http.StatusConflict, "AlreadyExists")
			return
		}
		s.events[path] = body
		if s.lose {
			reply(http.StatusInternalServerError, "InternalError")
			return
		}
		w.WriteHeader(http.StatusCreated)
		_ = json.NewEncoder(w).Encode(body)
	case http.MethodPatch:
		e, ok := s.events[r.URL.Path]
		switch {
		case !ok:
			reply(http.StatusNotFound, "NotFound")
		case r.Header.Get("Content-Type") != client.MergePatch:
			reply(http.StatusUnsupportedMediaType, "UnsupportedMediaType")
		default:
			maps.Copy(e, body)
			_ = json.NewEncoder(w).Encode(e)
		}
	default:
		reply(http.StatusMethodNotAllowed, "MethodNotAllowed")
	}
}

// take returns the requests since the last call, as method and path.
func (s *eventServer) take() []string {
	s.mu.Lock()
	defer s.mu.Unlock()
	reqs := s.reqs
	s.reqs = nil
	return reqs
}

// stored returns the Events in the order the writer named them, which is
// the order it created them in.
func (s *eventServer) stored() []map[string]any {
	s.mu.Lock()
	defer s.mu.Unlock()
	var out []map[string]any
	for _, p := range slices.Sorted(maps.Keys(s.events)) {
		out = append(out, s.events[p])
	}
	return out
}

func (s *eventServer) clear() {
	s.mu.Lock()
	defer s.mu.Unlock()
	clear(s.events)
}

func newTestEventWriter(t *testing.T) (*eventWriter, *eventServer, *bytes.Buffer) {
	t.Helper()
	srv := &eventServer{events: map[string]map[string]any{}}
	ts := httptest.NewServer(srv)
	t.Cleanup(ts.Close)
	c, err := client.New(&client.Config{Host: ts.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	var logs bytes.Buffer
	w := newEventWriter(c, slog.New(slog.NewTextHandler(&logs, nil)), newMetrics())
	w.host = "node-1"
	return w, srv, &logs
}

var t0 = time.Date(2026, 1, 2, 3, 4, 5, 123456789, time.UTC)

func widgetEvent(reason, note string, at time.Time) eventRecord {
	return eventRecord{
		eventKey: eventKey{
			controller: "widgets", action: "Reconcile", typ: Normal, reason: reason, note: note,
			regarding: eventRef{APIVersion: "example.dev/v1", Kind: "Widget", Namespace: "shop", Name: "w1", UID: "u1"},
		},
		at: at,
	}
}

func seriesOf(e map[string]any) any { return e["series"] }

func wantSeries(count int, last time.Time) any {
	return map[string]any{"count": float64(count), "lastObservedTime": last.Format(microTime)}
}

func methods(reqs []string) []string {
	var out []string
	for _, r := range reqs {
		out = append(out, strings.Fields(r)[0])
	}
	return out
}

func TestEventWriterCreatesAnEventThenCountsRepeats(t *testing.T) {
	w, srv, _ := newTestEventWriter(t)
	ctx := t.Context()
	w.record(ctx, widgetEvent("Pushed", "pushed", t0))
	if reqs := srv.take(); !slices.Equal(reqs, []string{"POST /apis/events.k8s.io/v1/namespaces/shop/events"}) {
		t.Fatalf("requests = %q", reqs)
	}
	events := srv.stored()
	if len(events) != 1 {
		t.Fatalf("stored %d Events, want 1", len(events))
	}
	name, _ := events[0]["metadata"].(map[string]any)["name"].(string)
	if want := fmt.Sprintf("w1.%x", t0.UnixNano()); name != want {
		t.Errorf("name = %q, want %q", name, want)
	}
	want := map[string]any{
		"apiVersion":          "events.k8s.io/v1",
		"kind":                "Event",
		"metadata":            map[string]any{"name": name, "namespace": "shop"},
		"eventTime":           "2026-01-02T03:04:05.123456Z",
		"reportingController": "widgets",
		"reportingInstance":   "widgets-node-1",
		"action":              "Reconcile",
		"reason":              "Pushed",
		"regarding":           map[string]any{"apiVersion": "example.dev/v1", "kind": "Widget", "namespace": "shop", "name": "w1", "uid": "u1"},
		"note":                "pushed",
		"type":                "Normal",
	}
	if !reflect.DeepEqual(events[0], want) {
		t.Errorf("Event =\n%v\nwant\n%v", events[0], want)
	}

	w.record(ctx, widgetEvent("Pushed", "pushed", t0.Add(time.Second)))
	if reqs := srv.take(); !slices.Equal(reqs, []string{"PATCH /apis/events.k8s.io/v1/namespaces/shop/events/" + name}) {
		t.Fatalf("the second time, requests = %q", reqs)
	}
	if got, want := seriesOf(srv.stored()[0]), wantSeries(2, t0.Add(time.Second)); !reflect.DeepEqual(got, want) {
		t.Errorf("the second time, series = %v, want %v", got, want)
	}

	w.record(ctx, widgetEvent("Pushed", "pushed", t0.Add(2*time.Second)))
	w.record(ctx, widgetEvent("Pushed", "pushed", t0.Add(3*time.Second)))
	if reqs := srv.take(); len(reqs) != 0 {
		t.Errorf("later repeats wrote %q before a flush", reqs)
	}
	w.flush(ctx, t0.Add(4*time.Second))
	if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"PATCH"}) {
		t.Errorf("flush: requests = %q", reqs)
	}
	if got, want := seriesOf(srv.stored()[0]), wantSeries(4, t0.Add(3*time.Second)); !reflect.DeepEqual(got, want) {
		t.Errorf("after a flush, series = %v, want %v", got, want)
	}
	w.flush(ctx, t0.Add(5*time.Second))
	if reqs := srv.take(); len(reqs) != 0 {
		t.Errorf("a flush without new repeats wrote %q", reqs)
	}
	for result, want := range map[string]float64{"created": 1, "updated": 2} {
		if got := w.metrics.counter("kube_events_total", "controller", "widgets", "result", result); got != want {
			t.Errorf("kube_events_total{result=%q} = %v, want %v", result, got, want)
		}
	}
}

func TestEventWriterKeepsDifferentEventsApart(t *testing.T) {
	w, srv, _ := newTestEventWriter(t)
	ctx := t.Context()
	w.record(ctx, widgetEvent("Pushed", "pushed", t0))
	w.record(ctx, widgetEvent("Rejected", "pushed", t0))
	warning := widgetEvent("Pushed", "pushed", t0)
	warning.typ = Warning
	w.record(ctx, warning)
	finalize := widgetEvent("Pushed", "pushed", t0)
	finalize.action = "Finalize"
	w.record(ctx, finalize)
	w.record(ctx, widgetEvent("Pushed", "pushed again", t0))
	recreated := widgetEvent("Pushed", "pushed", t0)
	recreated.regarding.UID = "u2"
	w.record(ctx, recreated)
	if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"POST", "POST", "POST", "POST", "POST", "POST"}) {
		t.Errorf("requests = %q, want a new Event each time", reqs)
	}
	events := srv.stored()
	if len(events) != 6 {
		t.Errorf("stored %d Events, want 6", len(events))
	}
	for _, e := range events {
		if seriesOf(e) != nil {
			t.Errorf("Event %v has a series", e)
		}
	}
}

func TestEventWriterEndsASeriesAfterAQuietPeriod(t *testing.T) {
	w, srv, _ := newTestEventWriter(t)
	ctx := t.Context()
	for i := range 3 {
		w.record(ctx, widgetEvent("Pushed", "pushed", t0.Add(time.Duration(i)*time.Second)))
	}
	srv.take()
	later := t0.Add(2*time.Second + w.finish)
	w.record(ctx, widgetEvent("Pushed", "pushed", later))
	if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"PATCH", "POST"}) {
		t.Errorf("requests = %q, want the old count written and then a new Event", reqs)
	}
	events := srv.stored()
	if len(events) != 2 {
		t.Fatalf("stored %d Events, want 2", len(events))
	}
	if got, want := seriesOf(events[0]), wantSeries(3, t0.Add(2*time.Second)); !reflect.DeepEqual(got, want) {
		t.Errorf("the first Event's series = %v, want %v", got, want)
	}
	if events[1]["eventTime"] != later.Format(microTime) || seriesOf(events[1]) != nil {
		t.Errorf("the second Event = %v", events[1])
	}

	w.flush(ctx, later.Add(w.finish-time.Nanosecond))
	if len(w.series) != 1 {
		t.Errorf("flush forgot a series that hasn't ended")
	}
	w.flush(ctx, later.Add(w.finish))
	if len(w.series) != 0 {
		t.Errorf("flush kept %d series that ended", len(w.series))
	}
	if reqs := srv.take(); len(reqs) != 0 {
		t.Errorf("flushes wrote %q", reqs)
	}
}

func TestEventWriterWritesEventsAboutClusterScopedObjectsInDefault(t *testing.T) {
	w, srv, _ := newTestEventWriter(t)
	r := widgetEvent("Pushed", "pushed", t0)
	r.regarding.Namespace = ""
	w.record(t.Context(), r)
	if reqs := srv.take(); !slices.Equal(reqs, []string{"POST /apis/events.k8s.io/v1/namespaces/default/events"}) {
		t.Fatalf("requests = %q", reqs)
	}
	if regarding := srv.stored()[0]["regarding"].(map[string]any); regarding["namespace"] != nil {
		t.Errorf("regarding = %v, want no namespace", regarding)
	}
}

func TestEventWriterCreatesADeletedEventAgain(t *testing.T) {
	w, srv, _ := newTestEventWriter(t)
	ctx := t.Context()
	w.record(ctx, widgetEvent("Pushed", "pushed", t0))
	srv.clear()
	w.record(ctx, widgetEvent("Pushed", "pushed", t0.Add(time.Second)))
	if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"POST", "PATCH", "POST"}) {
		t.Errorf("requests = %q", reqs)
	}
	events := srv.stored()
	if len(events) != 1 || !reflect.DeepEqual(seriesOf(events[0]), wantSeries(2, t0.Add(time.Second))) {
		t.Errorf("Events = %v, want one with a count of 2", events)
	}
	if got := w.metrics.counter("kube_events_total", "controller", "widgets", "result", "created"); got != 2 {
		t.Errorf("kube_events_total{result=\"created\"} = %v, want 2", got)
	}
}

func TestEventWriterStopsSendingARejectedEvent(t *testing.T) {
	w, srv, logs := newTestEventWriter(t)
	ctx := t.Context()
	srv.fail = http.StatusForbidden
	w.record(ctx, widgetEvent("Pushed", "pushed", t0))
	srv.fail = 0
	w.record(ctx, widgetEvent("Pushed", "pushed", t0.Add(time.Second)))
	w.flush(ctx, t0.Add(2*time.Second))
	if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"POST"}) {
		t.Errorf("requests = %q, want only the rejected one", reqs)
	}
	if got := w.metrics.counter("kube_events_total", "controller", "widgets", "result", "failed"); got != 1 {
		t.Errorf("kube_events_total{result=\"failed\"} = %v, want 1", got)
	}
	if !strings.Contains(logs.String(), "writing event failed") || !strings.Contains(logs.String(), "Forbidden") {
		t.Errorf("logs = %s", logs)
	}

	w.record(ctx, widgetEvent("Pushed", "pushed", t0.Add(time.Second+w.finish)))
	if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"POST"}) || len(srv.stored()) != 1 {
		t.Errorf("after the series ended, requests = %q and Events = %v, want a new Event", reqs, srv.stored())
	}
}

func TestEventWriterRetriesAfterATemporaryFailure(t *testing.T) {
	for _, code := range []int{http.StatusTooManyRequests, http.StatusInternalServerError} {
		w, srv, _ := newTestEventWriter(t)
		ctx := t.Context()
		srv.fail = code
		w.record(ctx, widgetEvent("Pushed", "pushed", t0))
		srv.fail = 0
		w.flush(ctx, t0.Add(time.Second))
		if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"POST", "POST"}) || len(srv.stored()) != 1 {
			t.Errorf("after a %d, requests = %q and Events = %v, want the Event created at the next flush", code, reqs, srv.stored())
		}
	}
}

func TestEventWriterHandlesALostResponse(t *testing.T) {
	w, srv, _ := newTestEventWriter(t)
	ctx := t.Context()
	srv.lose = true
	w.record(ctx, widgetEvent("Pushed", "pushed", t0))
	srv.lose = false
	w.flush(ctx, t0.Add(time.Second))
	if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"POST", "POST"}) {
		t.Errorf("requests = %q", reqs)
	}
	if got := w.metrics.counter("kube_events_total", "controller", "widgets", "result", "created"); got != 1 {
		t.Errorf("an Event that already exists counts as created: kube_events_total{result=\"created\"} = %v", got)
	}

	srv.lose = true
	w.record(ctx, widgetEvent("Rejected", "rejected", t0))
	srv.lose = false
	w.record(ctx, widgetEvent("Rejected", "rejected", t0.Add(time.Second)))
	if reqs := srv.take(); !slices.Equal(methods(reqs), []string{"POST", "POST", "PATCH"}) {
		t.Errorf("a repeat after a lost response: requests = %q", reqs)
	}
	events := srv.stored()
	if len(events) != 2 || !reflect.DeepEqual(seriesOf(events[1]), wantSeries(2, t0.Add(time.Second))) {
		t.Errorf("Events = %v", events)
	}
}

func TestEventWriterSendDropsEventsInsteadOfBlocking(t *testing.T) {
	w, _, logs := newTestEventWriter(t)
	w.queue = make(chan eventRecord, 2)
	c := &core{name: "widgets", ti: &typeInfo{apiVersion: "example.dev/v1", kind: "Widget"}}
	obj := &ObjectMeta{Namespace: "shop", Name: "w1", UID: "u1", ResourceVersion: "7"}
	s := &scope{}
	for i := range 3 {
		s.events = append(s.events, eventIntent{Event: Event{Type: Normal, Reason: "Pushed", Note: fmt.Sprint(i)}, at: t0})
	}
	w.send(c, obj, "Reconcile", s)
	if len(w.queue) != 2 {
		t.Fatalf("queued %d events, want 2", len(w.queue))
	}
	if got := w.metrics.counter("kube_events_total", "controller", "widgets", "result", "dropped"); got != 1 {
		t.Errorf("kube_events_total{result=\"dropped\"} = %v, want 1", got)
	}
	if got, want := <-w.queue, widgetEvent("Pushed", "0", t0); got != want {
		t.Errorf("queued %+v, want %+v", got, want)
	}
	w.flush(t.Context(), t0)
	if !strings.Contains(logs.String(), "dropped events") || !strings.Contains(logs.String(), "events=1") {
		t.Errorf("logs = %s", logs)
	}
	var nilWriter *eventWriter
	nilWriter.send(c, obj, "Reconcile", s)
}

func TestEventWriterWritesQueuedEventsWhenItStops(t *testing.T) {
	w, srv, _ := newTestEventWriter(t)
	stop := w.start()
	for i := range 3 {
		w.queue <- widgetEvent("Pushed", "pushed", t0.Add(time.Duration(i)*time.Second))
	}
	stop()
	events := srv.stored()
	if len(events) != 1 || !reflect.DeepEqual(seriesOf(events[0]), wantSeries(3, t0.Add(2*time.Second))) {
		t.Errorf("Events = %v, want one with a count of 3", events)
	}
}

func TestEventNames(t *testing.T) {
	w := &eventWriter{}
	ref := eventRef{Kind: "ClusterRole", Name: "w1"}
	if a, b := w.name(ref, t0), w.name(ref, t0); a != fmt.Sprintf("w1.%x", t0.UnixNano()) || b != fmt.Sprintf("w1.%x", t0.UnixNano()+1) {
		t.Errorf("names = %q, %q, want different names for events at the same time", a, b)
	}
	for _, name := range []string{"system:controller:w1", strings.Repeat("a", 237)} {
		ref.Name = name
		if got := w.name(ref, t0); !strings.HasPrefix(got, "clusterrole.") {
			t.Errorf("the name for %q is %q, want one that starts with the kind", name, got)
		}
	}
	ref.Name = strings.Repeat("a", 236)
	if got := w.name(ref, t0); !strings.HasPrefix(got, ref.Name+".") || len(got) > 253 {
		t.Errorf("the name for a long object name is %q", got)
	}
}

func TestTruncateNote(t *testing.T) {
	if got := truncateNote("pushed"); got != "pushed" {
		t.Errorf("truncateNote(pushed) = %q", got)
	}
	for _, s := range []string{strings.Repeat("a", 2000), strings.Repeat("é", 600)} {
		got := truncateNote(s)
		if len(got) > maxNote || len(got) < maxNote-3 || !utf8.ValidString(got) || !strings.HasSuffix(got, "...") {
			t.Errorf("truncateNote of %d bytes = %d bytes that end %q", len(s), len(got), got[max(0, len(got)-5):])
		}
	}
}

func TestEventfInFake(t *testing.T) {
	w := &widget{}
	w.Namespace, w.Name = "shop", "w1"
	ctx, rec := Fake(t.Context(), w)
	Eventf(ctx, Normal, "Created", "created %d pods", 3)
	Eventf(ctx, Warning, "Rejected", "no")
	want := []Event{{Type: Normal, Reason: "Created", Note: "created 3 pods"}, {Type: Warning, Reason: "Rejected", Note: "no"}}
	if got := rec.Events(); !reflect.DeepEqual(got, want) {
		t.Errorf("Events = %+v, want %+v", got, want)
	}
	rec.s.fail(errors.New("listing pods failed"))
	Eventf(ctx, Normal, "Created", "created pods")
	if got := rec.Events(); len(got) != 2 {
		t.Errorf("after a failure, Events = %+v, want no more", got)
	}
}

type eventfValidator struct{}

func (eventfValidator) Validate(ctx context.Context, _, _ *configMapMeta) error {
	Eventf(ctx, Normal, "Validated", "validated")
	return nil
}

func TestWebhooksCantRecordEvents(t *testing.T) {
	ti, _ := typeInfoFor[configMapMeta, *configMapMeta]()
	r := validate[configMapMeta, *configMapMeta](t.Context(), testManager(), ti, eventfValidator{}, &admissionRequest{Operation: "CREATE", Object: json.RawMessage(`{"metadata":{"name":"cm"}}`)})
	if r.Allowed || !strings.Contains(r.Result.Message, "kube.Eventf can't be called in a webhook") {
		t.Errorf("response = %+v", r.Result)
	}
}
