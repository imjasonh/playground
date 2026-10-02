package kube

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"maps"
	"net/http"
	"net/http/httptest"
	"net/url"
	"slices"
	"strconv"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

type cfgMap struct {
	Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
	Data   map[string]string `json:"data,omitempty"`
}

// fakeAPI serves list and watch for ConfigMaps in one namespace, with
// switches for the server behaviors an informer must handle.
type fakeAPI struct {
	mu        sync.Mutex
	objs      map[string]map[string]any
	rv        int
	streaming bool
	expire    bool // answer the next resumed watch with 410 Gone
	events    chan string
	drop      chan struct{}
	lists     []url.Values
	watches   []url.Values
}

func newFakeAPI(t *testing.T, streaming bool) (*fakeAPI, *client.Client) {
	t.Helper()
	f := &fakeAPI{objs: map[string]map[string]any{}, streaming: streaming, events: make(chan string, 100), drop: make(chan struct{})}
	srv := httptest.NewServer(f)
	t.Cleanup(srv.Close)
	c, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	return f, c
}

func (f *fakeAPI) obj(name string, data any) map[string]any {
	f.rv++
	o := map[string]any{
		"metadata": map[string]any{"name": name, "namespace": "ns", "resourceVersion": strconv.Itoa(f.rv)},
		"data":     data,
	}
	return o
}

// set stores an object without sending an event, as if the event were lost.
func (f *fakeAPI) set(name string, data any) map[string]any {
	f.mu.Lock()
	defer f.mu.Unlock()
	o := f.obj(name, data)
	f.objs[name] = o
	return o
}

// put stores an object and sends its watch event.
func (f *fakeAPI) put(name string, data any) {
	f.mu.Lock()
	_, existed := f.objs[name]
	f.mu.Unlock()
	o := f.set(name, data)
	typ := client.Added
	if existed {
		typ = client.Modified
	}
	f.send(typ, o)
}

func (f *fakeAPI) del(name string, silently bool) {
	f.mu.Lock()
	o := f.objs[name]
	delete(f.objs, name)
	f.rv++
	o["metadata"].(map[string]any)["resourceVersion"] = strconv.Itoa(f.rv)
	f.mu.Unlock()
	if !silently {
		f.send(client.Deleted, o)
	}
}

func (f *fakeAPI) send(typ string, o map[string]any) {
	b, _ := json.Marshal(map[string]any{"type": typ, "object": o})
	f.events <- string(b)
}

func (f *fakeAPI) bookmark(rv int, initialEnd bool) string {
	meta := map[string]any{"resourceVersion": strconv.Itoa(rv)}
	if initialEnd {
		meta["annotations"] = map[string]string{client.InitialEventsEndAnnotation: "true"}
	}
	b, _ := json.Marshal(map[string]any{"type": client.Bookmark, "object": map[string]any{"metadata": meta}})
	return string(b)
}

func (f *fakeAPI) calls() (lists, watches []url.Values) {
	f.mu.Lock()
	defer f.mu.Unlock()
	return slices.Clone(f.lists), slices.Clone(f.watches)
}

func (f *fakeAPI) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	q := r.URL.Query()
	f.mu.Lock()
	if q.Get("watch") != "1" {
		f.lists = append(f.lists, q)
		names := slices.Sorted(maps.Keys(f.objs))
		start, _ := strconv.Atoi(q.Get("continue"))
		limit, _ := strconv.Atoi(q.Get("limit"))
		end := len(names)
		if limit > 0 && start+limit < end {
			end = start + limit
		}
		var items []any
		for _, n := range names[start:end] {
			items = append(items, f.objs[n])
		}
		meta := map[string]any{"resourceVersion": strconv.Itoa(f.rv)}
		if end < len(names) {
			meta["continue"] = strconv.Itoa(end)
		}
		f.mu.Unlock()
		_ = json.NewEncoder(w).Encode(map[string]any{"kind": "ConfigMapList", "apiVersion": "v1", "metadata": meta, "items": items})
		return
	}
	f.watches = append(f.watches, q)
	flusher := w.(http.Flusher)
	switch {
	case q.Get("sendInitialEvents") == "true" && !f.streaming:
		f.mu.Unlock()
		w.WriteHeader(http.StatusUnprocessableEntity)
		fmt.Fprint(w, `{"kind":"Status","status":"Failure","reason":"Invalid","code":422,"message":"sendInitialEvents is forbidden"}`)
		return
	case q.Get("sendInitialEvents") == "true":
		for _, n := range slices.Sorted(maps.Keys(f.objs)) {
			b, _ := json.Marshal(map[string]any{"type": client.Added, "object": f.objs[n]})
			fmt.Fprintln(w, string(b))
		}
		fmt.Fprintln(w, f.bookmark(f.rv, true))
	case f.expire:
		f.expire = false
		f.mu.Unlock()
		fmt.Fprintln(w, `{"type":"ERROR","object":{"kind":"Status","status":"Failure","reason":"Expired","code":410,"message":"too old resource version"}}`)
		return
	}
	f.mu.Unlock()
	flusher.Flush()
	for {
		select {
		case line := <-f.events:
			fmt.Fprintln(w, line)
			flusher.Flush()
		case <-f.drop:
			return
		case <-r.Context().Done():
			return
		}
	}
}

type notification struct {
	key     string
	initial bool
	deleted bool
}

func startInformer(t *testing.T, c *client.Client, streaming bool) (*informer[cfgMap, *cfgMap], func() []notification) {
	t.Helper()
	ti, err := typeInfoFor[cfgMap, *cfgMap]()
	if err != nil {
		t.Fatal(err)
	}
	cfg := informerConfig{streaming: streaming, pageSize: 2, intern: true}
	inf := newInformer[cfgMap, *cfgMap](1, ti, resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}, c, cfg, slog.New(slog.NewTextHandler(io.Discard, nil)), nil)
	var mu sync.Mutex
	var got []notification
	inf.addHandler(func(old, new *cfgMap, initial bool) {
		mu.Lock()
		defer mu.Unlock()
		if new == nil {
			got = append(got, notification{key: old.Name, initial: initial, deleted: true})
			return
		}
		got = append(got, notification{key: new.Name, initial: initial})
	})
	ctx, cancel := context.WithCancel(t.Context())
	t.Cleanup(cancel)
	go inf.run(ctx)
	waitCtx, waitCancel := context.WithTimeout(ctx, 5*time.Second)
	defer waitCancel()
	if err := inf.waitSynced(waitCtx); err != nil {
		t.Fatalf("waitSynced: %v", err)
	}
	return inf, func() []notification {
		mu.Lock()
		defer mu.Unlock()
		return slices.Clone(got)
	}
}

func waitFor(t *testing.T, what string, cond func() bool) {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for !cond() {
		if time.Now().After(deadline) {
			t.Fatalf("timed out waiting for %s", what)
		}
		time.Sleep(10 * time.Millisecond)
	}
}

func keys(inf *informer[cfgMap, *cfgMap]) []string {
	var out []string
	inf.store.each("", func(o *cfgMap) bool { out = append(out, o.Name); return true })
	slices.Sort(out)
	return out
}

func TestInformerPaginatedListThenWatch(t *testing.T) {
	f, c := newFakeAPI(t, false)
	for _, n := range []string{"a", "b", "c"} {
		f.set(n, map[string]string{"v": n})
	}
	inf, notes := startInformer(t, c, false)

	lists, _ := f.calls()
	if len(lists) != 2 || lists[0].Get("limit") != "2" || lists[1].Get("continue") != "2" {
		t.Errorf("list calls = %v, want two pages", lists)
	}
	if got := keys(inf); !slices.Equal(got, []string{"a", "b", "c"}) {
		t.Errorf("cache = %v", got)
	}
	for _, n := range notes() {
		if !n.initial {
			t.Errorf("initial list notification %+v isn't marked initial", n)
		}
	}

	f.put("b", map[string]string{"v": "changed"})
	f.put("d", map[string]string{"v": "d"})
	f.del("a", false)
	waitFor(t, "watch events", func() bool { return len(notes()) == 6 })
	if got := keys(inf); !slices.Equal(got, []string{"b", "c", "d"}) {
		t.Errorf("cache = %v", got)
	}
	if b := inf.get(Key{"ns", "b"}).(*cfgMap); b.Data["v"] != "changed" || b.Kind != "ConfigMap" || b.APIVersion != "v1" {
		t.Errorf("b = %+v", b)
	}
	if want := []notification{{key: "b"}, {key: "d"}, {key: "a", deleted: true}}; !slices.Equal(notes()[3:], want) {
		t.Errorf("watch notifications = %+v, want %+v", notes()[3:], want)
	}
}

func TestInformerStreamingList(t *testing.T) {
	f, c := newFakeAPI(t, true)
	f.set("a", nil)
	f.set("b", nil)
	inf, _ := startInformer(t, c, true)
	lists, watches := f.calls()
	if len(lists) != 0 {
		t.Errorf("made %d list calls, want none with streaming lists", len(lists))
	}
	if len(watches) != 1 || watches[0].Get("resourceVersionMatch") != "NotOlderThan" {
		t.Errorf("watches = %v", watches)
	}
	if got := keys(inf); !slices.Equal(got, []string{"a", "b"}) {
		t.Errorf("cache = %v", got)
	}
	f.put("c", nil)
	waitFor(t, "event after streaming list", func() bool { return len(keys(inf)) == 3 })
}

func TestInformerFallsBackWhenStreamingIsUnsupported(t *testing.T) {
	f, c := newFakeAPI(t, false)
	f.set("a", nil)
	inf, _ := startInformer(t, c, true)
	lists, watches := f.calls()
	if len(lists) != 1 || len(watches) < 1 || watches[0].Get("sendInitialEvents") != "true" {
		t.Errorf("lists = %v, watches = %v; want a rejected streaming list, then a list", lists, watches)
	}
	if got := keys(inf); !slices.Equal(got, []string{"a"}) {
		t.Errorf("cache = %v", got)
	}
	if inf.streaming.Load() {
		t.Error("informer still tries streaming lists")
	}
}

func TestInformerResumesFromLastResourceVersion(t *testing.T) {
	f, c := newFakeAPI(t, false)
	f.set("a", nil)
	_, _ = startInformer(t, c, false)
	waitFor(t, "first watch", func() bool { _, w := f.calls(); return len(w) == 1 })
	f.events <- f.bookmark(100, false)
	time.Sleep(50 * time.Millisecond)
	f.drop <- struct{}{}
	waitFor(t, "second watch", func() bool { _, w := f.calls(); return len(w) == 2 })
	_, watches := f.calls()
	if rv := watches[1].Get("resourceVersion"); rv != "100" {
		t.Errorf("resumed at resourceVersion %q, want the bookmark's 100", rv)
	}
	if watches[1].Get("allowWatchBookmarks") != "true" {
		t.Error("watch doesn't ask for bookmarks")
	}
}

func TestInformerRelistsWhenResourceVersionExpires(t *testing.T) {
	f, c := newFakeAPI(t, false)
	f.set("a", nil)
	f.set("b", nil)
	inf, notes := startInformer(t, c, false)
	waitFor(t, "first watch", func() bool { _, w := f.calls(); return len(w) == 1 })

	// The informer misses these changes, then learns its resource version
	// is too old.
	f.del("a", true)
	f.set("c", nil)
	f.mu.Lock()
	f.expire = true
	f.mu.Unlock()
	f.drop <- struct{}{}

	waitFor(t, "relist", func() bool { return slices.Equal(keys(inf), []string{"b", "c"}) })
	lists, _ := f.calls()
	if len(lists) != 2 {
		t.Errorf("list calls = %d, want a relist", len(lists))
	}
	var after []notification
	for _, n := range notes() {
		if !n.initial {
			after = append(after, n)
		}
	}
	slices.SortFunc(after, func(a, b notification) int { return compare(a.key, b.key) })
	if want := []notification{{key: "a", deleted: true}, {key: "c"}}; !slices.Equal(after, want) {
		t.Errorf("relist notifications = %+v, want %+v", after, want)
	}
}

func compare(a, b string) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func TestInformerToleratesFieldTypeMismatch(t *testing.T) {
	f, c := newFakeAPI(t, false)
	f.set("a", map[string]any{"count": 3})
	f.set("b", map[string]string{"ok": "yes"})
	inf, _ := startInformer(t, c, false)
	if got := keys(inf); !slices.Equal(got, []string{"a", "b"}) {
		t.Errorf("cache = %v, want both objects despite a's mismatched field", got)
	}
}

func TestWaitSyncedReportsFirstFailure(t *testing.T) {
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusForbidden)
		fmt.Fprint(w, `{"kind":"Status","status":"Failure","reason":"Forbidden","code":403,"message":"configmaps is forbidden"}`)
	}))
	defer srv.Close()
	c, _ := client.New(&client.Config{Host: srv.URL}, "test")
	ti, _ := typeInfoFor[cfgMap, *cfgMap]()
	inf := newInformer[cfgMap, *cfgMap](1, ti, resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}, c, informerConfig{}, slog.New(slog.NewTextHandler(io.Discard, nil)), nil)
	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	go inf.run(ctx)
	if err := inf.waitSynced(ctx); !client.IsForbidden(err) {
		t.Errorf("waitSynced = %v, want the 403", err)
	}
}
