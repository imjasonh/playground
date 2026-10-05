package kube

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"reflect"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

func assign(members []string, n int) []string {
	out := make([]string, n)
	for i := range out {
		out[i] = rendezvous(members, i)
	}
	return out
}

func TestRendezvousMovesOnlyTheChangedMembersShards(t *testing.T) {
	const n = 64
	before := assign([]string{"a", "b", "c"}, n)
	counts := map[string]int{}
	for _, m := range before {
		counts[m]++
	}
	for _, m := range []string{"a", "b", "c"} {
		if counts[m] < n/6 {
			t.Errorf("member %s got %d of %d shards", m, counts[m], n)
		}
	}
	joined := assign([]string{"a", "b", "c", "d"}, n)
	for i := range n {
		if joined[i] != before[i] && joined[i] != "d" {
			t.Errorf("shard %d moved from %s to %s when d joined", i, before[i], joined[i])
		}
	}
	left := assign([]string{"a", "c"}, n)
	for i := range n {
		if before[i] != "b" && left[i] != before[i] {
			t.Errorf("shard %d moved from %s to %s when b left", i, before[i], left[i])
		}
	}
	if got := rendezvous([]string{"only"}, 3); got != "only" {
		t.Errorf("one member: %q", got)
	}
}

func TestShardOfSpreadsKeys(t *testing.T) {
	s := &sharder{n: 8}
	counts := make([]int, s.n)
	for i := range 8000 {
		counts[s.shardOf(Key{Namespace: fmt.Sprintf("ns-%d", i%7), Name: fmt.Sprintf("obj-%d", i)})]++
	}
	for i, c := range counts {
		if c < 700 || c > 1300 {
			t.Errorf("shard %d has %d of 8000 keys", i, c)
		}
	}
	if (&sharder{n: 1}).shardOf(Key{Name: "x"}) != 0 {
		t.Error("with one shard, every key is in shard 0")
	}
}

func TestObservationJudgesExpiryByLocalTime(t *testing.T) {
	var o observation
	l := &lease{}
	l.Spec.HolderIdentity, l.Spec.LeaseDurationSeconds = "a", 15
	// The holder's clock is far behind; its renew time means nothing here.
	l.Spec.RenewTime = "2001-01-01T00:00:00.000000Z"
	now := time.Now()
	if o.expired(l, now) {
		t.Error("a lease seen for the first time is current")
	}
	if !o.expired(l, now.Add(16*time.Second)) {
		t.Error("a lease not renewed for longer than its duration is expired")
	}
	l.Spec.RenewTime = "2001-01-01T00:00:10.000000Z"
	if o.expired(l, now.Add(17*time.Second)) {
		t.Error("a renewed lease is current")
	}
	l.Spec.HolderIdentity = ""
	if !o.expired(l, now.Add(18*time.Second)) {
		t.Error("a released lease is expired")
	}
}

// leaseAPI answers a sharder with one shard the way the API server does,
// keeping the shard's Lease, and records status writes.
type leaseAPI struct {
	mu       sync.Mutex
	lease    *lease
	statuses []map[string]any
}

func (a *leaseAPI) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	a.mu.Lock()
	defer a.mu.Unlock()
	switch {
	case strings.HasSuffix(r.URL.Path, "/status"):
		var obj map[string]any
		if err := json.NewDecoder(r.Body).Decode(&obj); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		a.statuses = append(a.statuses, obj)
		_ = json.NewEncoder(w).Encode(obj)
	case r.Method == http.MethodGet && strings.HasSuffix(r.URL.Path, "/leases"):
		items := []*lease{}
		if a.lease != nil {
			items = append(items, a.lease)
		}
		_ = json.NewEncoder(w).Encode(map[string]any{"items": items})
	case r.Method == http.MethodGet && a.lease == nil:
		http.NotFound(w, r)
	case r.Method == http.MethodGet:
		_ = json.NewEncoder(w).Encode(a.lease)
	case r.Method == http.MethodPost, r.Method == http.MethodPut:
		var l lease
		if err := json.NewDecoder(r.Body).Decode(&l); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		a.lease = &l
		_ = json.NewEncoder(w).Encode(&l)
	default:
		http.Error(w, "unexpected request", http.StatusMethodNotAllowed)
	}
}

// setHolder makes holder the shard's holder, as another replica would.
func (a *leaseAPI) setHolder(holder string) {
	a.mu.Lock()
	defer a.mu.Unlock()
	l := *a.lease
	l.Spec.HolderIdentity = holder
	l.Spec.RenewTime = time.Now().UTC().Format(microTime)
	a.lease = &l
}

func (a *leaseAPI) statusWrites() []map[string]any {
	a.mu.Lock()
	defer a.mu.Unlock()
	return slices.Clone(a.statuses)
}

// TestRetakenShardRequiresTheResourceVersionAgain holds a reconcile's status
// write while the replica loses the object's shard and takes it back. The
// write succeeds, but its reconcile read the cache before the replica that
// held the shard in between could write the object. So the next status write
// must still require the cached resource version.
func TestRetakenShardRequiresTheResourceVersionAgain(t *testing.T) {
	api := &leaseAPI{}
	srv := httptest.NewServer(api)
	t.Cleanup(srv.Close)
	cl, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	m := testManager()
	m.client, m.Name, m.LeaseNamespace = cl, "widgets", "shop"
	s := newSharder(m)
	w := &widget{}
	w.Namespace, w.Name, w.UID, w.ResourceVersion = "shop", "w1", "u1", "5"
	c := triggerable(t, m, resolved{apiVersion: "example.dev/v1", plural: "widgets", namespaced: true}, w)
	c.sh = s
	s.sync(t.Context())
	if !s.owns(w.Key()) {
		t.Fatal("the replica didn't take the free shard")
	}
	held := c.precondition(w.Key(), w)

	t.Log("Another replica takes the shard and releases it, and this replica takes it back.")
	api.setHolder("other")
	s.sync(t.Context())
	if s.owns(w.Key()) {
		t.Fatal("the replica still holds the shard that another replica took")
	}
	api.setHolder("")
	s.sync(t.Context())
	if !s.owns(w.Key()) {
		t.Fatal("the replica didn't take the released shard back")
	}

	first := *w
	if err := c.writeStatus(t.Context(), w, &first, nil, held); err != nil {
		t.Fatal(err)
	}
	next := *w
	if err := c.writeStatus(t.Context(), w, &next, nil, c.precondition(w.Key(), w)); err != nil {
		t.Fatal(err)
	}
	writes := api.statusWrites()
	if len(writes) != 2 {
		t.Fatalf("%d status writes, want 2", len(writes))
	}
	for i, body := range writes {
		meta, _ := body["metadata"].(map[string]any)
		if meta["resourceVersion"] != "5" {
			t.Errorf("status write %d required resource version %v, want the cached 5", i+1, meta["resourceVersion"])
		}
	}
}

// TestFinalizerPatchRequiresTheAppliedResourceVersion removes a finalizer
// that another field manager also lists, while writes to the object require
// the cached resource version. The apply leaves the finalizer listed and
// returns a new resource version. The JSON patch that then removes the
// finalizer must require that version, and a conflict on it means that
// something wrote the object in between, so it fails as stale.
func TestFinalizerPatchRequiresTheAppliedResourceVersion(t *testing.T) {
	m := testManager()
	w := &widget{}
	w.Namespace, w.Name, w.UID, w.ResourceVersion = "shop", "w1", "u1", "5"
	c := triggerable(t, m, resolved{apiVersion: "example.dev/v1", plural: "widgets", namespaced: true}, w)
	w.Finalizers = []string{"example.dev/other", c.finalizer}
	patches := make(chan []byte, 1)
	srv := httptest.NewServer(http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
		switch r.Header.Get("Content-Type") {
		case client.ApplyPatch:
			_ = json.NewEncoder(rw).Encode(map[string]any{"metadata": map[string]any{
				"name": w.Name, "namespace": w.Namespace, "uid": w.UID, "resourceVersion": "6", "finalizers": w.Finalizers,
			}})
		case client.JSONPatch:
			b, err := io.ReadAll(r.Body)
			if err != nil {
				http.Error(rw, err.Error(), http.StatusBadRequest)
				return
			}
			patches <- b
			http.Error(rw, "the object has been modified", http.StatusConflict)
		default:
			http.Error(rw, "unexpected request", http.StatusMethodNotAllowed)
		}
	}))
	t.Cleanup(srv.Close)
	cl, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	m.client = cl

	rv := w.ResourceVersion
	if err := c.setFinalizer(t.Context(), w, false, "", &rv); !errors.Is(err, errStale) {
		t.Errorf("setFinalizer = %v, want a stale error", err)
	}
	var ops []map[string]any
	select {
	case b := <-patches:
		if err := json.Unmarshal(b, &ops); err != nil {
			t.Fatal(err)
		}
	default:
		t.Fatal("setFinalizer sent no JSON patch")
	}
	want := map[string]any{"op": "replace", "path": "/metadata/resourceVersion", "value": "6"}
	if !slices.ContainsFunc(ops, func(op map[string]any) bool { return reflect.DeepEqual(op, want) }) {
		t.Errorf("patch %v doesn't require the resource version that the apply returned", ops)
	}
}

// TestFinalizerRemovalShowsTheCacheCaughtUp reconciles an object whose status
// needs no write and whose finalizer the framework removes, while writes to
// the object require the cached resource version. The removal succeeds,
// which shows that the controller's cache had caught up, so later writes
// needn't require a version. But if the cache that Get reads holds an older
// version, the reconcile may have read out-of-date data there, and later
// writes still must.
func TestFinalizerRemovalShowsTheCacheCaughtUp(t *testing.T) {
	for _, tt := range []struct {
		name     string
		getRV    string
		caughtUp bool
	}{
		{name: "Get agrees", getRV: "5", caughtUp: true},
		{name: "Get is behind", getRV: "4", caughtUp: false},
	} {
		t.Run(tt.name, func(t *testing.T) {
			srv := httptest.NewServer(http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
				if r.Header.Get("Content-Type") != client.ApplyPatch {
					http.Error(rw, "unexpected request", http.StatusMethodNotAllowed)
					return
				}
				_ = json.NewEncoder(rw).Encode(map[string]any{"metadata": map[string]any{
					"name": "w1", "namespace": "shop", "uid": "u1", "resourceVersion": "6",
				}})
			}))
			t.Cleanup(srv.Close)
			cl, err := client.New(&client.Config{Host: srv.URL}, "test")
			if err != nil {
				t.Fatal(err)
			}
			m := testManager()
			m.client, m.tracker = cl, newTracker()
			res := resolved{apiVersion: "example.dev/v1", plural: "widgets", namespaced: true}
			c := triggerable[widget](t, m, res)
			c.sh = &sharder{n: 1, shards: []*shard{{}}}
			w := &widget{}
			w.Namespace, w.Name, w.UID, w.ResourceVersion = "shop", "w1", "u1", "5"
			w.Finalizers = []string{c.finalizer}
			synced := syncedCondition(nil, 0)
			synced.LastTransitionTime = time.Unix(1, 0).UTC()
			w.Status.Conditions = []Condition{synced}
			c.primary.store.put(w)
			viaGet := *w
			viaGet.ResourceVersion = tt.getRV
			get := newInformer[widget, *widget](2, c.ti, res, nil, informerConfig{}, m.log, m.metrics)
			get.store.put(&viaGet)
			m.resolved = map[*typeInfo]resolved{c.ti: res}
			m.caches = map[cacheKey]cache{{ti: c.ti}: get}

			if _, err := c.reconcileKey(t.Context(), w.Key()); err != nil {
				t.Fatal(err)
			}
			if got := c.hasCaughtUp(w.Key(), 0); got != tt.caughtUp {
				t.Errorf("caught up = %v, want %v", got, tt.caughtUp)
			}
		})
	}
}

// TestStaleReconcileKeepsTheLastError fails a reconcile's status write as
// invalid, then fails the next one as stale, while writes to the object
// require the cached resource version. The retry of a stale reconcile redoes
// it, so LastError must still return the invalid write's error.
func TestStaleReconcileKeepsTheLastError(t *testing.T) {
	var code atomic.Int32
	srv := httptest.NewServer(http.HandlerFunc(func(rw http.ResponseWriter, r *http.Request) {
		http.Error(rw, "refused", int(code.Load()))
	}))
	t.Cleanup(srv.Close)
	cl, err := client.New(&client.Config{Host: srv.URL}, "test")
	if err != nil {
		t.Fatal(err)
	}
	m := testManager()
	m.client, m.tracker = cl, newTracker()
	w := &widget{}
	w.Namespace, w.Name, w.UID, w.ResourceVersion = "shop", "w1", "u1", "5"
	c := triggerable(t, m, resolved{apiVersion: "example.dev/v1", plural: "widgets", namespaced: true}, w)
	c.sh = &sharder{n: 1, shards: []*shard{{}}}

	code.Store(http.StatusUnprocessableEntity)
	c.process(t.Context(), w.Key())
	invalid := c.lastError(w.Key())
	if !client.IsInvalid(invalid) {
		t.Fatalf("LastError = %v, want the invalid status write", invalid)
	}
	code.Store(http.StatusConflict)
	c.process(t.Context(), w.Key())
	if n := m.metrics.counter("kube_reconcile_total", "controller", c.name, "result", "stale"); n != 1 {
		t.Fatalf("%v reconciles failed as stale, want 1", n)
	}
	if err := c.lastError(w.Key()); err != invalid {
		t.Errorf("LastError after a stale reconcile = %v, want %v", err, invalid)
	}
}

// TestDeleteForgetsAnObjectInAShardThatIsntHeld deletes an object in a shard
// that this replica doesn't hold, so the replica doesn't reconcile it. The
// replica must still forget what it recorded for the object, or it keeps
// that state for as long as it runs.
func TestDeleteForgetsAnObjectInAShardThatIsntHeld(t *testing.T) {
	m := testManager()
	m.tracker = newTracker()
	w := &widget{}
	w.Namespace, w.Name = "shop", "w1"
	c := triggerable[widget](t, m, resolved{apiVersion: "example.dev/v1", plural: "widgets", namespaced: true})
	c.sh = &sharder{n: 1, shards: []*shard{{}}}
	k, ak := w.Key(), appliedKey{ti: c.ti, key: w.Key()}
	c.setApplied(k, map[appliedKey]uint64{ak: 1})
	c.setStatus(k, 1, true)
	c.setStatusApply(k, 1)
	c.setCaughtUp(k, 0)
	m.tracker.add(ref{c: &c.core, key: k}, dep{src: 1, ns: "shop", name: "config"}, nil)

	c.onPrimary(w, nil, false)
	if high, low := c.q.Len(); high+low != 0 {
		t.Errorf("queue = %d high, %d low; want no reconcile", high, low)
	}
	if _, ok := c.lastApplied(k, ak); ok {
		t.Error("the replica remembers what it applied for the deleted object")
	}
	if _, ok := c.lastStatus(k); ok {
		t.Error("the replica remembers the deleted object's status")
	}
	if _, ok := c.lastStatusApply(k); ok {
		t.Error("the replica remembers the status that it applied to the deleted object")
	}
	if c.hasCaughtUp(k, 0) {
		t.Error("the replica remembers that its cache caught up with the deleted object")
	}
	if n := m.tracker.size(); n != 0 {
		t.Errorf("the replica tracks %d dependencies of the deleted object, want 0", n)
	}
}

func TestNilSharderOwnsEverything(t *testing.T) {
	var s *sharder
	if !s.owns(Key{Name: "x"}) {
		t.Error("nil sharder doesn't own a key")
	}
	if _, ok := s.begin(Key{Name: "x"}); !ok {
		t.Error("nil sharder doesn't begin a key")
	}
	s.end(0)
	s.onAcquire(func(int) {})
}
