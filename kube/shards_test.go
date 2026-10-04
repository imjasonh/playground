package kube

import (
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"sync"
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
