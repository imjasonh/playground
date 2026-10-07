package kube

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"maps"
	"net/http"
	"net/http/httptest"
	"net/url"
	"slices"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

type cfgMap struct {
	Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
	Data   map[string]string `json:"data,omitempty"`
}

// fakeAPI serves list and watch for ConfigMaps in one namespace, with
// switches for the server behaviors an informer must handle. Unlike
// Kubernetes, its discovery lists a status subresource for ConfigMaps.
type fakeAPI struct {
	mu        sync.Mutex
	objs      map[string]map[string]any
	rv        int
	streaming bool
	expire    bool   // answer the next resumed watch with 410 Gone
	onList    func() // runs once, between reading and sending the next list
	events    chan string
	drop      chan struct{}
	lists     []url.Values
	watches   []url.Values
	write     http.HandlerFunc // serves requests other than GET
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

// unlockAfterList unlocks f.mu, which must be held, and then runs onList.
func (f *fakeAPI) unlockAfterList() {
	onList := f.onList
	f.onList = nil
	f.mu.Unlock()
	if onList != nil {
		onList()
	}
}

func (f *fakeAPI) calls() (lists, watches []url.Values) {
	f.mu.Lock()
	defer f.mu.Unlock()
	return slices.Clone(f.lists), slices.Clone(f.watches)
}

func (f *fakeAPI) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if r.URL.Path == "/api/v1" {
		fmt.Fprint(w, `{"kind":"APIResourceList","groupVersion":"v1","resources":[{"name":"configmaps","namespaced":true,"kind":"ConfigMap"},{"name":"configmaps/status","namespaced":true,"kind":"ConfigMap"}]}`)
		return
	}
	q := r.URL.Query()
	f.mu.Lock()
	if write := f.write; write != nil && r.Method != http.MethodGet {
		f.mu.Unlock()
		write(w, r)
		return
	}
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
		f.unlockAfterList()
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
		var initial []string
		for _, n := range slices.Sorted(maps.Keys(f.objs)) {
			b, _ := json.Marshal(map[string]any{"type": client.Added, "object": f.objs[n]})
			initial = append(initial, string(b))
		}
		initial = append(initial, f.bookmark(f.rv, true))
		f.unlockAfterList()
		for _, line := range initial {
			fmt.Fprintln(w, line)
		}
	case f.expire:
		f.expire = false
		f.mu.Unlock()
		fmt.Fprintln(w, `{"type":"ERROR","object":{"kind":"Status","status":"Failure","reason":"Expired","code":410,"message":"too old resource version"}}`)
		return
	default:
		f.mu.Unlock()
	}
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
	return startInformerFor[cfgMap](t, c, streaming)
}

func startInformerFor[T any, P Resource[T]](t *testing.T, c *client.Client, streaming bool) (*informer[T, P], func() []notification) {
	t.Helper()
	return startInformerWith[T, P](t, c, streaming, slog.New(slog.NewTextHandler(io.Discard, nil)))
}

func startInformerWith[T any, P Resource[T]](t *testing.T, c *client.Client, streaming bool, log *slog.Logger) (*informer[T, P], func() []notification) {
	t.Helper()
	ti, err := typeInfoFor[T, P]()
	if err != nil {
		t.Fatal(err)
	}
	cfg := informerConfig{streaming: streaming, pageSize: 2, intern: true}
	inf := newInformer[T, P](1, ti, resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}, c, cfg, log, nil)
	var mu sync.Mutex
	var got []notification
	inf.addHandler(func(old, new *T, initial bool) {
		mu.Lock()
		defer mu.Unlock()
		if new == nil {
			got = append(got, notification{key: metaOf[T, P](old).Name, initial: initial, deleted: true})
			return
		}
		got = append(got, notification{key: metaOf[T, P](new).Name, initial: initial})
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

func keys[T any, P Resource[T]](inf *informer[T, P]) []string {
	var out []string
	inf.store.each("", func(o *T) bool { out = append(out, metaOf[T, P](o).Name); return true })
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

func TestInformerBacksOffWhenWatchesEndEarly(t *testing.T) {
	const a = `{"metadata":{"name":"a","namespace":"ns","resourceVersion":"10"}}`
	for _, streaming := range []bool{false, true} {
		t.Run(fmt.Sprintf("streaming=%t", streaming), func(t *testing.T) {
			// Like a proxy that ends every watch at once, which cuts each
			// streaming list after its first event.
			var lists, streams, watches atomic.Int64
			srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				q := r.URL.Query()
				switch {
				case q.Get("watch") != "1":
					lists.Add(1)
					fmt.Fprintf(w, `{"kind":"ConfigMapList","apiVersion":"v1","metadata":{"resourceVersion":"10"},"items":[%s]}`, a)
				case q.Get("sendInitialEvents") == "true":
					streams.Add(1)
					fmt.Fprintf(w, `{"type":"ADDED","object":%s}`+"\n", a)
				default:
					watches.Add(1)
				}
			}))
			t.Cleanup(srv.Close)
			c, err := client.New(&client.Config{Host: srv.URL}, "test")
			if err != nil {
				t.Fatal(err)
			}
			ti, err := typeInfoFor[cfgMap, *cfgMap]()
			if err != nil {
				t.Fatal(err)
			}
			inf := newInformer[cfgMap, *cfgMap](1, ti, resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}, c, informerConfig{streaming: streaming}, slog.New(slog.NewTextHandler(io.Discard, nil)), nil)
			ctx, cancel := context.WithCancel(t.Context())
			t.Cleanup(cancel)
			go inf.run(ctx)
			select {
			case <-inf.synced:
			case <-time.After(10 * time.Second):
				t.Fatalf("the informer didn't sync after %d streaming lists", streams.Load())
			}
			if got := keys(inf); !slices.Equal(got, []string{"a"}) {
				t.Errorf("cache = %v", got)
			}
			var want int64
			if streaming {
				want = maxListCuts
			}
			if got := streams.Load(); got != want || lists.Load() != 1 {
				t.Errorf("%d streaming lists and %d lists, want %d and 1", got, lists.Load(), want)
			}
			if inf.streaming.Load() {
				t.Error("informer still tries streaming lists")
			}

			// The backoff starts at 800ms.
			before := watches.Load()
			time.Sleep(time.Second)
			if n := watches.Load() - before; n > 3 {
				t.Errorf("%d watches in a second, want at most 3", n)
			}
		})
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

func TestInformerDoesntShowWritesThatOverlapAList(t *testing.T) {
	for _, streaming := range []bool{false, true} {
		t.Run(fmt.Sprintf("streaming=%t", streaming), func(t *testing.T) {
			f, c := newFakeAPI(t, streaming)
			f.set("a", map[string]string{"v": "1"})
			f.set("b", map[string]string{"v": "1"})
			inf, _ := startInformer(t, c, streaming)
			waitFor(t, "first watch", func() bool { _, w := f.calls(); return len(w) == 1 })
			ka, kb := Key{"ns", "a"}, Key{"ns", "b"}
			read := func(k Key) string {
				if o, ok := inf.get(k).(*cfgMap); ok {
					return o.Data["v"]
				}
				return ""
			}
			watched := func(k Key) string {
				inf.store.mu.RLock()
				defer inf.store.mu.RUnlock()
				if o := inf.store.objs[k.Namespace][k.Name]; o != nil {
					return o.Data["v"]
				}
				return ""
			}
			respond := func(end func(*written), o map[string]any) {
				b, err := json.Marshal(o)
				if err != nil {
					t.Error(err)
				}
				end(&written{obj: b})
			}

			t.Log("The informer misses a change to a, and its watch expires during a write to b that the list holds.")
			f.set("a", map[string]string{"v": "2"})
			endB := inf.begin(kb)
			wroteB := f.set("b", map[string]string{"v": "2"})
			var wroteA map[string]any
			listed := make(chan struct{})
			f.mu.Lock()
			f.expire = true
			f.onList = func() {
				defer close(listed)
				// The write to a ends after the list reads the objects, so
				// the list doesn't hold it.
				endA := inf.begin(ka)
				wroteA = f.set("a", map[string]string{"v": "3"})
				respond(endA, wroteA)
				if got := read(ka); got != "1" {
					t.Errorf("during the list, a = %s, want 1", got)
				}
			}
			f.mu.Unlock()
			f.drop <- struct{}{}
			select {
			case <-listed:
			case <-time.After(5 * time.Second):
				t.Fatal("the informer didn't list again")
			}
			waitFor(t, "the list", func() bool { return watched(ka) == "2" })
			respond(endB, wroteB)
			if a, b := read(ka), read(kb); a != "2" || b != "2" {
				t.Errorf("after the list, a = %s and b = %s, want 2 and 2", a, b)
			}

			t.Log("The watch delivers the write to a, and another client's change to b.")
			f.send(client.Modified, wroteA)
			f.put("b", map[string]string{"v": "3"})
			waitFor(t, "the watch events", func() bool { return watched(ka) == "3" && watched(kb) == "3" })
			if a, b := read(ka), read(kb); a != "3" || b != "3" {
				t.Errorf("after the watch events, a = %s and b = %s, want 3 and 3", a, b)
			}
			inf.store.mu.RLock()
			writes, flights := len(inf.store.writes), len(inf.store.flights)
			inf.store.mu.RUnlock()
			if writes != 0 || flights != 0 {
				t.Errorf("store holds %d writes and %d writes in progress, want none", writes, flights)
			}
		})
	}
}

func TestInformerIgnoresChangesThatTheTypeCantSee(t *testing.T) {
	f, c := newFakeAPI(t, false)
	f.set("a", map[string]string{"v": "1"})
	inf, notes := startInformer(t, c, false)
	waitFor(t, "first watch", func() bool { _, w := f.calls(); return len(w) == 1 })
	watched := func() []notification { return notes()[1:] }

	t.Log("A new resource version alone, or a change to binaryData, which cfgMap doesn't declare, notifies no one.")
	f.put("a", map[string]string{"v": "1"})
	o := f.set("a", map[string]string{"v": "1"})
	o["binaryData"] = map[string]string{"b": "AA=="}
	f.send(client.Modified, o)
	f.put("a", map[string]string{"v": "2"})
	waitFor(t, "the change to data", func() bool { return len(watched()) > 0 })
	if want := []notification{{key: "a"}}; !slices.Equal(watched(), want) {
		t.Errorf("watch notifications = %+v, want only %+v for the change to data", watched(), want)
	}
	f.mu.Lock()
	rv := f.objs["a"]["metadata"].(map[string]any)["resourceVersion"]
	f.mu.Unlock()
	if got := inf.get(Key{"ns", "a"}).(*cfgMap).ResourceVersion; got != rv {
		t.Errorf("cached resourceVersion = %s, want %s: the cache keeps every version", got, rv)
	}

	t.Log("A relist that finds a new resource version and nothing else new notifies no one.")
	f.set("a", map[string]string{"v": "2"})
	f.set("b", nil)
	f.mu.Lock()
	f.expire = true
	f.mu.Unlock()
	f.drop <- struct{}{}
	waitFor(t, "relist", func() bool { return slices.Equal(keys(inf), []string{"a", "b"}) })
	if want := []notification{{key: "a"}, {key: "b"}}; !slices.Equal(watched(), want) {
		t.Errorf("notifications after relist = %+v, want %+v", watched(), want)
	}
}

type cfgMeta struct {
	Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
}

func TestMetadataOnlyInformerSeesEveryResourceVersion(t *testing.T) {
	f, c := newFakeAPI(t, false)
	f.set("a", map[string]string{"v": "1"})
	_, notes := startInformerFor[cfgMeta](t, c, false)
	waitFor(t, "first watch", func() bool { _, w := f.calls(); return len(w) == 1 })
	f.put("a", map[string]string{"v": "1"})
	waitFor(t, "a notification for the new resource version", func() bool { return len(notes()) == 2 })
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

// port is an int32 that decodes itself, as IntOrString does.
type port int32

func (p *port) UnmarshalJSON(b []byte) error { return json.Unmarshal(b, (*int32)(p)) }

// strictMap is a ConfigMap whose data holds fields that some JSON values
// don't fit.
type strictMap struct {
	Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
	Data   struct {
		Count   int       `json:"count,omitempty"`
		Port    port      `json:"port,omitempty"`
		Targets []string  `json:"targets,omitempty"`
		When    time.Time `json:"when,omitzero"`
	} `json:"data"`
}

func TestInformerSkipsObjectsThatDontDecode(t *testing.T) {
	for _, streaming := range []bool{false, true} {
		t.Run(fmt.Sprintf("streaming=%t", streaming), func(t *testing.T) {
			f, c := newFakeAPI(t, streaming)
			f.set("good", map[string]any{"count": 1})
			f.set("plain", map[string]any{"count": "three"})
			f.set("time", map[string]any{"when": "2024-01-01t10:00:00z"})
			// port's error stops encoding/json before it reaches targets.
			f.set("custom", map[string]any{"port": 3000000000, "targets": []string{"a"}})
			inf, notes := startInformerFor[strictMap](t, c, streaming)
			if got := keys(inf); !slices.Equal(got, []string{"good"}) {
				t.Errorf("cache = %v, want only good", got)
			}
			if n := inf.undecodable(); n != 3 {
				t.Errorf("undecodable = %d, want 3", n)
			}

			t.Log("A version that decodes ends a skip, a version that doesn't starts one, and a delete ends one.")
			f.put("time", map[string]any{"when": "2024-01-01T10:00:00Z"})
			f.put("good", map[string]any{"port": 3000000000})
			f.del("plain", false)
			f.put("later", nil)
			waitFor(t, "the watch events", func() bool { return len(notes()) == 4 })
			if want := []notification{{key: "time"}, {key: "good", deleted: true}, {key: "later"}}; !slices.Equal(notes()[1:], want) {
				t.Errorf("watch notifications = %+v, want %+v", notes()[1:], want)
			}
			if got := keys(inf); !slices.Equal(got, []string{"later", "time"}) {
				t.Errorf("cache = %v, want later and time", got)
			}
			if n := inf.undecodable(); n != 2 {
				t.Errorf("undecodable = %d, want 2", n)
			}
			if _, watches := f.calls(); len(watches) != 1 {
				t.Errorf("%d watches, want 1", len(watches))
			}
		})
	}
}

// warnings records the key and error of each warning.
type warnings struct {
	mu  sync.Mutex
	got []string
}

func (w *warnings) Enabled(_ context.Context, l slog.Level) bool { return l >= slog.LevelWarn }
func (w *warnings) WithAttrs([]slog.Attr) slog.Handler           { return w }
func (w *warnings) WithGroup(string) slog.Handler                { return w }

func (w *warnings) Handle(_ context.Context, r slog.Record) error {
	var key, err string
	r.Attrs(func(a slog.Attr) bool {
		switch a.Key {
		case "key":
			key = a.Value.String()
		case "err":
			err = a.Value.String()
		}
		return true
	})
	w.mu.Lock()
	defer w.mu.Unlock()
	w.got = append(w.got, key+": "+err)
	return nil
}

func (w *warnings) list() []string {
	w.mu.Lock()
	defer w.mu.Unlock()
	return slices.Clone(w.got)
}

func TestInformerWarnsOnceAboutEachErrorInAnObject(t *testing.T) {
	f, c := newFakeAPI(t, false)
	f.set("a", map[string]any{"when": "noon"})
	w := &warnings{}
	inf, _ := startInformerWith[strictMap](t, c, false, slog.New(w))
	if got := w.list(); len(got) != 1 || !strings.HasPrefix(got[0], "ns/a: ") || !strings.Contains(got[0], "noon") {
		t.Fatalf("warnings = %q, want one about ns/a", got)
	}

	t.Log("Neither a new version with the same error nor a relist warns again.")
	f.put("a", map[string]any{"when": "noon"})
	f.put("b", nil)
	waitFor(t, "b", func() bool { return slices.Equal(keys(inf), []string{"b"}) })
	f.set("c", nil)
	f.mu.Lock()
	f.expire = true
	f.mu.Unlock()
	f.drop <- struct{}{}
	waitFor(t, "relist", func() bool { return slices.Equal(keys(inf), []string{"b", "c"}) })
	if got := w.list(); len(got) != 1 {
		t.Errorf("warnings = %q, want only the first", got)
	}

	t.Log("Another error warns again.")
	f.put("a", map[string]any{"when": "midnight"})
	waitFor(t, "another warning", func() bool { return len(w.list()) == 2 })
	if got := w.list()[1]; !strings.HasPrefix(got, "ns/a: ") || !strings.Contains(got, "midnight") {
		t.Errorf("second warning = %q", got)
	}
}

func TestUndecodableObjectsMetric(t *testing.T) {
	m := &Manager{client: &client.Client{}, Logger: slog.New(slog.NewTextHandler(io.Discard, nil))}
	if err := m.init(); err != nil {
		t.Fatal(err)
	}
	ti, err := typeInfoFor[cfgMap, *cfgMap]()
	if err != nil {
		t.Fatal(err)
	}
	newCache := func(selector string, skipped ...string) cache {
		inf := newInformer[cfgMap, *cfgMap](1, ti, resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}, nil, informerConfig{namespace: "ns", selector: selector}, m.log, nil)
		for _, name := range skipped {
			inf.store.skip(&decodeError{meta: ObjectMeta{Name: name, Namespace: "ns"}, err: errors.New("bad")})
		}
		return inf
	}
	m.caches[cacheKey{ti: ti, namespace: "ns"}] = newCache("", "a", "b")
	m.unshared = []cache{newCache("app=web", "a"), newCache("app=web", "a"), newCache("app=db")}
	var b strings.Builder
	m.metrics.write(&b)
	const name = `kube_cache_undecodable_objects{type="ConfigMap.v1",namespace="ns",selector=`
	for _, want := range []string{name + `""} 2`, name + `"app=web"} 1`, name + `"app=db"} 0`} {
		if !strings.Contains(b.String(), want+"\n") {
			t.Errorf("metrics output is missing %q:\n%s", want, b.String())
		}
	}
	if n := strings.Count(b.String(), name+`"app=web"}`); n != 1 {
		t.Errorf("%d samples for the two caches with selector app=web, want 1", n)
	}
}

func TestInformersReadProtobufWhenTheSchemaHasTheirFields(t *testing.T) {
	type futurePod struct {
		Object `kube:"apiVersion=v1,kind=Pod"`
		Spec   struct {
			WarpDrive bool `json:"warpDrive"`
		} `json:"spec"`
	}
	type podMeta struct {
		Object `kube:"apiVersion=v1,kind=Pod"`
	}
	log := slog.New(slog.NewTextHandler(io.Discard, nil))
	for _, tc := range []struct {
		name  string
		info  func() (*typeInfo, error)
		proto bool
	}{
		{"Pod", typeInfoFor[benchPodFull, *benchPodFull], true},
		{"ConfigMap", typeInfoFor[cfgMap, *cfgMap], true},
		{"metadata only", typeInfoFor[podMeta, *podMeta], true},
		{"a field the schema lacks", typeInfoFor[futurePod, *futurePod], false},
		{"custom type", typeInfoFor[gizmo, *gizmo], false},
	} {
		ti, err := tc.info()
		if err != nil {
			t.Fatal(err)
		}
		if got := protoPlan(ti, log) != nil; got != tc.proto {
			t.Errorf("%s: protobuf = %v, want %v", tc.name, got, tc.proto)
		}
	}
	ti, _ := typeInfoFor[cfgMap, *cfgMap]()
	res := resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}
	if got := newInformer[cfgMap, *cfgMap](1, ti, res, nil, informerConfig{protobuf: true}, log, nil).accept(true); got != protoAccept {
		t.Errorf("Accept = %q, want %q", got, protoAccept)
	}
	if got := newInformer[cfgMap, *cfgMap](1, ti, res, nil, informerConfig{}, log, nil).accept(true); got != "" {
		t.Errorf("with protobuf off, Accept = %q", got)
	}
	mi, _ := typeInfoFor[podMeta, *podMeta]()
	if got := newInformer[podMeta, *podMeta](1, mi, res, nil, informerConfig{protobuf: true}, log, nil).accept(false); got != protoWatchAccept {
		t.Errorf("metadata-only watch Accept = %q, want %q", got, protoWatchAccept)
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
