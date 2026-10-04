package kube

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"maps"
	"net/http"
	"slices"
	"strconv"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

type counted struct {
	Object `kube:"apiVersion=v1,kind=ConfigMap,plural=configmaps,scope=Namespaced"`
	Status struct {
		Count int `json:"count,omitempty"`
	} `json:"status,omitzero"`
}

// stepper raises an object's status count by one in each reconcile, up to n,
// and records the count that each reconcile read.
type stepper struct {
	n    int
	mu   sync.Mutex
	seen []int
}

func (s *stepper) Reconcile(ctx context.Context, o *counted) error {
	s.mu.Lock()
	s.seen = append(s.seen, o.Status.Count)
	s.mu.Unlock()
	if o.Status.Count < s.n {
		o.Status.Count++
		RequeueAfter(ctx, time.Millisecond)
	}
	return nil
}

func (s *stepper) counts() []int {
	s.mu.Lock()
	defer s.mu.Unlock()
	return slices.Clone(s.seen)
}

func TestReconcileSeesItsOwnStatusWrite(t *testing.T) {
	for _, tc := range []struct {
		name string
		opts []Option
	}{
		{"shared cache", nil},
		{"unshared cache", []Option{WatchSelector("app=web")}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			const n = 5
			f, c := newFakeAPI(t, true)
			// The fake API server holds back the watch events for status
			// writes, so a reconcile can read a written status only from
			// the write's response.
			var held []string
			f.mu.Lock()
			f.objs["a"] = map[string]any{"metadata": map[string]any{
				"name": "a", "namespace": "ns", "uid": "a-uid", "resourceVersion": "1", "labels": map[string]any{"app": "web"},
			}}
			f.rv = 1
			f.write = func(w http.ResponseWriter, r *http.Request) {
				var body struct {
					Status any `json:"status"`
				}
				if r.Method != http.MethodPatch || r.URL.Path != "/api/v1/namespaces/ns/configmaps/a/status" || json.NewDecoder(r.Body).Decode(&body) != nil {
					http.Error(w, "unexpected write", http.StatusBadRequest)
					return
				}
				f.mu.Lock()
				defer f.mu.Unlock()
				f.rv++
				o := maps.Clone(f.objs["a"])
				meta := maps.Clone(o["metadata"].(map[string]any))
				meta["resourceVersion"] = strconv.Itoa(f.rv)
				o["metadata"], o["status"] = meta, body.Status
				f.objs["a"] = o
				b, _ := json.Marshal(map[string]any{"type": client.Modified, "object": o})
				held = append(held, string(b))
				_ = json.NewEncoder(w).Encode(o)
			}
			f.mu.Unlock()
			writes := func() []string {
				f.mu.Lock()
				defer f.mu.Unlock()
				return slices.Clone(held)
			}

			r := &stepper{n: n}
			ctl := For[counted](r, append(tc.opts, Named("stepper"))...)
			m := &Manager{client: c, Logger: slog.New(slog.NewTextHandler(io.Discard, nil)), DisableProtobuf: true}
			ctx, cancel := context.WithCancel(t.Context())
			done := make(chan error, 1)
			go func() { done <- m.Run(ctx, ctl) }()
			t.Cleanup(func() {
				cancel()
				if err := <-done; err != nil {
					t.Errorf("Run: %v", err)
				}
			})

			waitFor(t, "reconciles", func() bool { return len(r.counts()) > n })
			want := make([]int, n+1)
			for i := range want {
				want[i] = i
			}
			if got := r.counts()[:n+1]; !slices.Equal(got, want) {
				t.Fatalf("reconciles read counts %v, want %v", got, want)
			}
			if got := len(writes()); got != n {
				t.Errorf("%d status writes, want %d", got, n)
			}

			for _, e := range writes() {
				f.events <- e
			}
			inf := ctl.(*controller[counted, *counted]).primary
			waitFor(t, "the watch to deliver the writes", func() bool {
				inf.store.mu.RLock()
				defer inf.store.mu.RUnlock()
				o := inf.store.objs["ns"]["a"]
				return o != nil && o.Status.Count == n && len(inf.store.writes) == 0
			})
			if got := r.counts()[n+1:]; slices.ContainsFunc(got, func(v int) bool { return v != n }) {
				t.Errorf("reconciles after the events read counts %v, want only %d", got, n)
			}
			if got := len(writes()); got != n {
				t.Errorf("%d status writes after the events, want %d", got, n)
			}
		})
	}
}

func TestStoreShowsOwnWrites(t *testing.T) {
	k := Key{"a", "one"}
	obj := func(rv, uid string) *widget {
		w := cm("a", "one", rv, nil, "a/parent")
		w.UID = uid
		return w
	}
	wrote := func(rv string) *ownWrite[widget] { return &ownWrite[widget]{obj: obj(rv, "u"), rv: rv, uid: "u"} }
	deleted := func(uid string) *ownWrite[widget] { return &ownWrite[widget]{uid: uid} }
	newStore := func() *store[widget, *widget] { return &store[widget, *widget]{ownerKey: "x/owner"} }
	// shows checks that get, each, and byOwner all read the version rv, or
	// no object if rv is empty.
	shows := func(t *testing.T, s *store[widget, *widget], rv string) {
		t.Helper()
		var got, each, owned, want []string
		if o := s.get(k); o != nil {
			got = append(got, o.ResourceVersion)
		}
		s.each("", func(o *widget) bool { each = append(each, o.ResourceVersion); return true })
		for _, o := range s.byOwner("a/parent") {
			owned = append(owned, o.ResourceVersion)
		}
		if rv != "" {
			want = []string{rv}
		}
		if !slices.Equal(got, want) || !slices.Equal(each, want) || !slices.Equal(owned, want) {
			t.Errorf("get = %v, each = %v, byOwner = %v; want %v", got, each, owned, want)
		}
	}
	settled := func(t *testing.T, s *store[widget, *widget]) {
		t.Helper()
		if len(s.writes) != 0 || len(s.flights) != 0 {
			t.Errorf("store holds %d writes and %d writes in progress, want none", len(s.writes), len(s.flights))
		}
	}

	t.Run("a write shows until its event arrives", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		s.end(s.begin(k), wrote("3"))
		shows(t, s, "3")
		s.put(obj("2", "u")) // someone else's earlier write
		shows(t, s, "3")
		s.put(obj("3", "u"))
		shows(t, s, "3")
		settled(t, s)
		s.put(obj("4", "u"))
		shows(t, s, "4")
	})

	t.Run("a write whose event arrives before its response", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		f := s.begin(k)
		s.put(obj("2", "u"))
		s.put(obj("3", "u")) // someone else's later write
		s.end(f, wrote("2"))
		shows(t, s, "3")
		settled(t, s)
	})

	t.Run("a write that changes nothing", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		s.end(s.begin(k), wrote("1"))
		shows(t, s, "1")
		settled(t, s)
	})

	t.Run("a failed write", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		s.end(s.begin(k), nil)
		shows(t, s, "1")
		settled(t, s)
	})

	t.Run("overlapping writes", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		f, g := s.begin(k), s.begin(k)
		s.end(f, wrote("2"))
		s.end(g, wrote("3"))
		shows(t, s, "1")
		settled(t, s)
		s.end(s.begin(k), wrote("4"))
		shows(t, s, "4")
	})

	t.Run("a list", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		s.end(s.begin(k), wrote("2"))
		f := s.begin(k)
		s.beginList()
		shows(t, s, "2")
		s.end(f, wrote("3")) // newer than the list
		shows(t, s, "2")
		s.replace(map[Key]*widget{k: obj("2", "u")})
		shows(t, s, "2")
		settled(t, s)
		s.put(obj("3", "u"))
		shows(t, s, "3")

		s.beginList()
		g := s.begin(k)
		s.replace(map[Key]*widget{k: obj("4", "u")})
		s.end(g, wrote("4")) // the list holds it
		shows(t, s, "4")
		settled(t, s)
		s.end(s.begin(k), wrote("5"))
		shows(t, s, "5")
	})

	t.Run("a delete", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		s.end(s.begin(k), deleted("u"))
		shows(t, s, "")
		s.put(obj("2", "u")) // an update before the delete
		shows(t, s, "")
		s.remove(obj("3", "u"))
		shows(t, s, "")
		settled(t, s)
		s.put(obj("4", "v"))
		shows(t, s, "4")
	})

	t.Run("a delete of an object that was replaced", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "v"))
		s.end(s.begin(k), deleted("u"))
		shows(t, s, "1")
		settled(t, s)
	})

	t.Run("a delete whose event arrives before its response", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		f := s.begin(k)
		s.remove(obj("2", "u"))
		s.end(f, deleted("u"))
		settled(t, s)
		s.put(obj("3", "v"))
		shows(t, s, "3")
	})

	t.Run("a create", func(t *testing.T) {
		s := newStore()
		s.end(s.begin(k), wrote("1"))
		shows(t, s, "1")
		s.put(obj("1", "u"))
		shows(t, s, "1")
		settled(t, s)
	})

	t.Run("a write that leaves the selector", func(t *testing.T) {
		s := newStore()
		s.put(obj("1", "u"))
		s.end(s.begin(k), &ownWrite[widget]{rv: "2", uid: "u"})
		shows(t, s, "")
		s.remove(obj("2", "u"))
		settled(t, s)
		s.put(obj("3", "u")) // it matches again
		shows(t, s, "3")
	})

	t.Run("a write outside the selector", func(t *testing.T) {
		s := newStore()
		s.end(s.begin(k), &ownWrite[widget]{rv: "2", uid: "u"})
		settled(t, s)
		s.put(obj("3", "u"))
		shows(t, s, "3")
	})
}

func TestStored(t *testing.T) {
	const deleting = `"deletionTimestamp":"2026-01-02T03:04:05Z"`
	for _, tc := range []struct {
		name    string
		resp    string
		deleted bool
		want    string // object, gone, or empty when unknown
	}{
		{"object", `{"metadata":{"uid":"u","resourceVersion":"2"}}`, false, "object"},
		{"field of another JSON type", `{"metadata":{"uid":"u","resourceVersion":"2"},"spec":{"finalizers":"f"}}`, false, "object"},
		{"no resource version", `{"metadata":{"uid":"u"}}`, false, ""},
		{"not an object", `[]`, false, ""},
		{"not JSON", `{`, false, ""},
		{"update that releases a deleting object", `{"metadata":{"uid":"u","resourceVersion":"2",` + deleting + `,"deletionGracePeriodSeconds":0}}`, false, "gone"},
		{"update of a deleting object with a finalizer", `{"metadata":{"uid":"u","resourceVersion":"2",` + deleting + `,"finalizers":["f"]}}`, false, "object"},
		{"update of a terminating pod", `{"metadata":{"uid":"u","resourceVersion":"2",` + deleting + `,"deletionGracePeriodSeconds":30}}`, false, "object"},
		{"delete that returns a status", `{"kind":"Status","apiVersion":"v1","metadata":{},"status":"Success","details":{"name":"a","kind":"configmaps","uid":"u"}}`, true, "gone"},
		{"delete that returns a status without a UID", `{"kind":"Status","apiVersion":"v1","metadata":{},"status":"Success"}`, true, ""},
		{"delete that returns the deleted object", `{"metadata":{"uid":"u","resourceVersion":"3"}}`, true, "gone"},
		{"delete that waits for a finalizer", `{"metadata":{"uid":"u","resourceVersion":"3",` + deleting + `,"finalizers":["f"]}}`, true, "object"},
		{"delete of a namespace", `{"metadata":{"uid":"u","resourceVersion":"3",` + deleting + `},"spec":{"finalizers":["kubernetes"]}}`, true, "object"},
		{"delete of a pod with a grace period", `{"metadata":{"uid":"u","resourceVersion":"3",` + deleting + `,"deletionGracePeriodSeconds":30}}`, true, "object"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			w := stored(json.RawMessage(tc.resp), tc.deleted)
			var got string
			switch {
			case w == nil:
			case w.gone:
				got = "gone"
			case string(w.obj) == tc.resp:
				got = "object"
			}
			if got != tc.want {
				t.Errorf("stored = %q (%+v), want %q", got, w, tc.want)
			}
			if w != nil && w.uid != "u" {
				t.Errorf("uid = %q, want u", w.uid)
			}
		})
	}
}

func testInformer[T any, P Resource[T]](t *testing.T, res resolved, cfg informerConfig) *informer[T, P] {
	t.Helper()
	ti, err := typeInfoFor[T, P]()
	if err != nil {
		t.Fatal(err)
	}
	return newInformer[T, P](1, ti, res, nil, cfg, slog.New(slog.NewTextHandler(io.Discard, nil)), nil)
}

func TestInformerTracksWritesItCanShow(t *testing.T) {
	configMaps := resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}
	if testInformer[counted](t, configMaps, informerConfig{namespace: "ns"}).begin(Key{"other", "a"}) != nil {
		t.Error("a cache of one namespace tracks a write in another")
	}
	if testInformer[counted](t, configMaps, informerConfig{selector: "size>3"}).begin(Key{"ns", "a"}) != nil {
		t.Error("a cache whose selector it can't evaluate tracks a write")
	}
	inf := testInformer[policy](t, resolved{apiVersion: "example.dev/v1", plural: "networkpolicies"}, informerConfig{})
	inf.begin(Key{"ns", "a"})(stored(json.RawMessage(`{"metadata":{"name":"a","uid":"u","resourceVersion":"1"}}`), false))
	if inf.get(Key{Name: "a"}) == nil {
		t.Error("a write of a cluster-scoped object doesn't show")
	}
}

func TestWritesShowInEveryCacheOfTheKind(t *testing.T) {
	f, c := newFakeAPI(t, false)
	var code int
	var body string
	f.mu.Lock()
	f.write = func(w http.ResponseWriter, _ *http.Request) {
		f.mu.Lock()
		defer f.mu.Unlock()
		w.WriteHeader(code)
		_, _ = io.WriteString(w, body)
	}
	f.mu.Unlock()
	respond := func(status int, resp string) {
		f.mu.Lock()
		defer f.mu.Unlock()
		code, body = status, resp
	}
	object := func(rv int, app string) string {
		return fmt.Sprintf(`{"apiVersion":"v1","kind":"ConfigMap","metadata":{"name":"a","namespace":"ns","uid":"u","resourceVersion":"%d","labels":{"app":%q}},"data":{"rv":"%d"},"status":{"count":%d}}`, rv, app, rv, rv)
	}

	configMaps := resolved{apiVersion: "v1", plural: "configmaps", namespaced: true}
	full := testInformer[counted](t, configMaps, informerConfig{})
	view := testInformer[cfgMap](t, configMaps, informerConfig{namespace: "ns", selector: "app=web"})
	other := testInformer[widget](t, resolved{apiVersion: "example.dev/v1", plural: "widgets", namespaced: true}, informerConfig{})
	m := &Manager{client: c, caches: map[cacheKey]cache{{ti: full.ti}: full, {ti: other.ti}: other}, unshared: []cache{view}}
	k, path := Key{"ns", "a"}, configMaps.path("ns", "a")
	// shows checks the count that full reads, and the rv label that view
	// reads, with 0 and "" for no object.
	shows := func(t *testing.T, count int, rv string) {
		t.Helper()
		var gotCount int
		var gotRV string
		if o, _ := full.get(k).(*counted); o != nil {
			gotCount = o.Status.Count
		}
		if o, _ := view.get(k).(*cfgMap); o != nil {
			gotRV = o.Data["rv"]
		}
		if gotCount != count || gotRV != rv {
			t.Errorf("caches show count %d and rv %q, want %d and %q", gotCount, gotRV, count, rv)
		}
	}
	ctx := t.Context()

	respond(http.StatusOK, object(1, "web"))
	if err := m.apply(ctx, full.ti, k, path, "test", map[string]any{}, nil); err != nil {
		t.Fatal(err)
	}
	shows(t, 1, "1")
	respond(http.StatusOK, object(2, "api"))
	if err := m.patch(ctx, full.ti, k, path, client.JSONPatch, []byte(`[]`)); err != nil {
		t.Fatal(err)
	}
	shows(t, 2, "")
	respond(http.StatusUnprocessableEntity, `{"kind":"Status","apiVersion":"v1","status":"Failure","reason":"Invalid","code":422}`)
	if err := m.apply(ctx, full.ti, k, path, "test", map[string]any{}, nil); !client.IsInvalid(err) {
		t.Fatalf("apply = %v, want Invalid", err)
	}
	shows(t, 2, "")
	respond(http.StatusOK, `{"kind":"Status","apiVersion":"v1","metadata":{},"status":"Success","details":{"name":"a","kind":"configmaps","uid":"u"}}`)
	if err := m.delete(ctx, full.ti, k, path, client.DeleteOptions{UID: "u"}); err != nil {
		t.Fatal(err)
	}
	shows(t, 0, "")

	respond(http.StatusOK, object(3, "web"))
	if err := m.apply(ctx, full.ti, k, path, "test", map[string]any{}, nil); err != nil {
		t.Fatal(err)
	}
	shows(t, 3, "3")
	respond(http.StatusConflict, `{"kind":"Status","apiVersion":"v1","status":"Failure","reason":"Conflict","code":409}`)
	if err := m.delete(ctx, full.ti, k, path, client.DeleteOptions{UID: "u"}); !client.IsConflict(err) {
		t.Fatalf("delete = %v, want Conflict", err)
	}
	shows(t, 3, "3")
	respond(http.StatusNotFound, `{"kind":"Status","apiVersion":"v1","status":"Failure","reason":"NotFound","code":404}`)
	if err := m.delete(ctx, full.ti, k, path, client.DeleteOptions{UID: "u"}); !client.IsNotFound(err) {
		t.Fatalf("delete = %v, want NotFound", err)
	}
	shows(t, 0, "")

	if other.store.writes != nil || other.store.flights != nil {
		t.Error("a write of a ConfigMap reached a cache of another kind")
	}
}
