package kube

import (
	"fmt"
	"testing"
	"time"
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
