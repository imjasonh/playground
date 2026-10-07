package kube

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"hash/fnv"
	"log/slog"
	"net/http"
	"net/url"
	"os"
	"slices"
	"strconv"
	"sync"
	"time"

	"github.com/imjasonh/playground/kube/internal/client"
)

// Lease timing, matching client-go's leader election defaults.
var (
	leaseDuration = 15 * time.Second
	renewDeadline = 10 * time.Second
	retryPeriod   = 2 * time.Second
	// memberExpiry is how long a replica's membership Lease can go without
	// renewal before another replica deletes it.
	memberExpiry = time.Minute
)

const microTime = "2006-01-02T15:04:05.000000Z07:00"

type lease struct {
	APIVersion string `json:"apiVersion"`
	Kind       string `json:"kind"`
	Metadata   struct {
		Name            string            `json:"name"`
		Namespace       string            `json:"namespace"`
		UID             string            `json:"uid,omitempty"`
		ResourceVersion string            `json:"resourceVersion,omitempty"`
		Labels          map[string]string `json:"labels,omitempty"`
	} `json:"metadata"`
	Spec struct {
		HolderIdentity       string `json:"holderIdentity,omitempty"`
		LeaseDurationSeconds int32  `json:"leaseDurationSeconds,omitempty"`
		AcquireTime          string `json:"acquireTime,omitempty"`
		RenewTime            string `json:"renewTime,omitempty"`
		LeaseTransitions     int32  `json:"leaseTransitions,omitempty"`
	} `json:"spec"`
}

// observation is when a lease's holder and renew time last changed, by this
// replica's clock. Judging expiry by local observation time makes leases
// immune to clock skew between replicas.
type observation struct {
	record string
	at     time.Time
}

// expired records l and reports whether it has run out: it has no holder, or
// its holder hasn't renewed it within its duration.
func (o *observation) expired(l *lease, now time.Time) bool {
	if record := l.Spec.HolderIdentity + "@" + l.Spec.RenewTime; record != o.record {
		o.record, o.at = record, now
	}
	if l.Spec.HolderIdentity == "" {
		return true
	}
	return !o.at.Add(time.Duration(l.Spec.LeaseDurationSeconds) * time.Second).After(now)
}

// sharder divides the keys that controllers reconcile into shards and holds
// some of them. Each shard is a Lease, and only the replica that holds a
// shard's Lease reconciles its keys. With one shard, this is leader
// election.
//
// With more shards, each replica also holds a membership Lease, so every
// replica knows which replicas are alive. Every replica computes the same
// assignment of shards to live replicas with rendezvous hashing, which moves
// few shards when replicas come and go. A replica acquires the free shards
// assigned to it. When a shard it holds is assigned to another live replica,
// it stops starting reconciles in that shard, waits for the ones in progress
// to finish, and releases the shard, so two replicas never reconcile one key
// at the same time. A free shard that its assigned replica doesn't take
// within a lease duration goes to any replica.
type sharder struct {
	m        *Manager
	n        int
	ns       string
	group    string
	identity string
	keys     labelKeys
	log      *slog.Logger

	mu        sync.Mutex
	shards    []*shard
	member    *lease // this replica's membership Lease as last written
	members   map[string]*observation
	acquired  []func(int)
	first     chan struct{}
	firstOnce sync.Once
}

type shard struct {
	name     string
	obs      observation
	held     bool
	tenure   uint64    // counts this replica's acquisitions of the shard
	renewed  time.Time // last successful write of the lease
	draining bool      // releasing: no new reconciles start
	inflight int
	free     time.Time // when the lease was first seen free; zero if held
}

func newSharder(m *Manager) *sharder {
	n := max(m.Shards, 1)
	host, _ := os.Hostname()
	suffix := make([]byte, 4)
	_, _ = rand.Read(suffix)
	s := &sharder{
		m: m, n: n, ns: m.ownNamespace(), group: objectName(m.Name),
		identity: host + "_" + hex.EncodeToString(suffix),
		keys:     newLabelKeys(),
		members:  map[string]*observation{},
		first:    make(chan struct{}),
	}
	s.log = m.log.With("identity", s.identity)
	for i := range n {
		name := s.group
		if n > 1 {
			name += "-shard-" + strconv.Itoa(i)
		}
		s.shards = append(s.shards, &shard{name: name})
	}
	m.metrics.gauge("kube_shards_held", "Shards whose lease this replica holds.", func() []sample {
		s.mu.Lock()
		defer s.mu.Unlock()
		held := 0
		for _, sh := range s.shards {
			if sh.held {
				held++
			}
		}
		return []sample{{value: float64(held)}}
	})
	return s
}

// shardOf returns the shard that k belongs to.
func (s *sharder) shardOf(k Key) int {
	if s.n == 1 {
		return 0
	}
	h := fnv.New32a()
	h.Write([]byte(k.Namespace))
	h.Write([]byte{'/'})
	h.Write([]byte(k.Name))
	return int(h.Sum32() % uint32(s.n))
}

// owns reports whether this replica holds k's shard and isn't releasing it.
func (s *sharder) owns(k Key) bool {
	if s == nil {
		return true
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	sh := s.shards[s.shardOf(k)]
	return sh.held && !sh.draining
}

// begin reports whether to reconcile k now, and if so counts the reconcile
// as in progress until end.
func (s *sharder) begin(k Key) (int, bool) {
	if s == nil {
		return 0, true
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	i := s.shardOf(k)
	sh := s.shards[i]
	if !sh.held || sh.draining {
		return i, false
	}
	sh.inflight++
	return i, true
}

func (s *sharder) end(i int) {
	if s == nil {
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	s.shards[i].inflight--
}

// tenure returns a number that changes each time this replica acquires k's
// shard.
func (s *sharder) tenure(k Key) uint64 {
	if s == nil {
		return 0
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.shards[s.shardOf(k)].tenure
}

// onAcquire calls fn with each shard this replica acquires from now on.
func (s *sharder) onAcquire(fn func(int)) {
	if s == nil {
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	s.acquired = append(s.acquired, fn)
}

// run keeps the shard leases until ctx is done. The caller releases them
// with releaseAll once reconciles have stopped.
func (s *sharder) run(ctx context.Context) {
	s.log.Info("waiting for shards", "shards", s.n, "namespace", s.ns)
	for {
		s.sync(ctx)
		select {
		case <-ctx.Done():
			return
		case <-time.After(retryPeriod):
		}
	}
}

func (s *sharder) leasePath(name string) string {
	return client.Path("coordination.k8s.io/v1", "leases", s.ns, name)
}

// sync renews this replica's leases and acquires and releases shards.
func (s *sharder) sync(ctx context.Context) {
	ctx, cancel := context.WithTimeout(ctx, retryPeriod)
	defer cancel()
	now := time.Now()
	if s.n > 1 {
		s.renewMembership(ctx, now)
	}
	leases, err := s.list(ctx)
	if err != nil {
		s.log.Warn("listing shard leases failed", "err", err)
	}
	live := s.liveMembers(ctx, leases, now)

	type action struct {
		i                 int
		l                 *lease
		renew, take, drop bool
	}
	var actions []action
	s.mu.Lock()
	for i, sh := range s.shards {
		l := leases[sh.name]
		expired := l == nil || sh.obs.expired(l, now)
		assigned := s.n == 1 || rendezvous(live, i) == s.identity
		switch {
		case sh.held && l != nil && l.Spec.HolderIdentity != "" && l.Spec.HolderIdentity != s.identity:
			s.lose(sh, "another replica holds it")
		case sh.held:
			if !assigned && !sh.draining {
				sh.draining = true
				s.log.Info("releasing shard to the replica it's assigned to", "shard", sh.name)
			}
			if sh.draining && sh.inflight == 0 {
				actions = append(actions, action{i: i, l: l, drop: true})
			} else {
				actions = append(actions, action{i: i, l: l, renew: true})
			}
		case expired:
			if sh.free.IsZero() {
				sh.free = now
			}
			if err == nil && (assigned || now.Sub(sh.free) > leaseDuration) {
				actions = append(actions, action{i: i, l: l, take: true})
			}
		default:
			sh.free = time.Time{}
		}
	}
	s.mu.Unlock()

	for _, a := range actions {
		sh := s.shards[a.i]
		switch {
		case a.drop:
			s.release(ctx, sh, a.l)
			s.mu.Lock()
			sh.held, sh.draining = false, false
			s.mu.Unlock()
			s.m.metrics.inc("kube_shard_transitions_total", "event", "released")
		case a.renew:
			ok := s.write(ctx, sh, a.l, now)
			s.mu.Lock()
			if ok {
				sh.renewed = now
			} else if now.Sub(sh.renewed) > renewDeadline {
				s.lose(sh, "renewing its lease failed")
			}
			s.mu.Unlock()
		case a.take:
			if !s.write(ctx, sh, a.l, now) {
				continue
			}
			s.mu.Lock()
			sh.held, sh.draining, sh.renewed, sh.free = true, false, now, time.Time{}
			sh.tenure++
			fns := slices.Clone(s.acquired)
			s.mu.Unlock()
			s.log.Info("acquired shard", "shard", sh.name)
			s.m.metrics.inc("kube_shard_transitions_total", "event", "acquired")
			for _, fn := range fns {
				fn(a.i)
			}
			s.firstOnce.Do(func() { close(s.first) })
		}
	}
}

// lose stops reconciling a shard's keys. Reconciles already running finish.
// The caller holds s.mu.
func (s *sharder) lose(sh *shard, why string) {
	sh.held, sh.draining = false, false
	s.log.Error("lost shard", "shard", sh.name, "reason", why)
	s.m.metrics.inc("kube_shard_transitions_total", "event", "lost")
}

// list returns the group's leases by name. A shard lease without the group
// label, written by something else, is read by name.
func (s *sharder) list(ctx context.Context) (map[string]*lease, error) {
	var list struct {
		Items []*lease `json:"items"`
	}
	err := s.m.client.Call(ctx, client.Request{
		Method: http.MethodGet,
		Path:   client.Path("coordination.k8s.io/v1", "leases", s.ns, ""),
		Query:  url.Values{"labelSelector": {s.keys.leaseGroup + "=" + s.group}},
	}, &list)
	if err != nil {
		return nil, err
	}
	out := map[string]*lease{}
	for _, l := range list.Items {
		out[l.Metadata.Name] = l
	}
	for _, sh := range s.shards {
		if _, ok := out[sh.name]; ok {
			continue
		}
		var l lease
		switch err := s.m.client.Get(ctx, s.leasePath(sh.name), &l); {
		case err == nil:
			out[sh.name] = &l
		case !client.IsNotFound(err):
			return nil, err
		}
	}
	return out, nil
}

// write makes this replica the holder of sh's lease l, creating it if l is
// nil. It reports whether the write succeeded.
func (s *sharder) write(ctx context.Context, sh *shard, l *lease, now time.Time) bool {
	stamp := now.UTC().Format(microTime)
	var err error
	if l == nil {
		var nl lease
		nl.APIVersion, nl.Kind = "coordination.k8s.io/v1", "Lease"
		nl.Metadata.Name, nl.Metadata.Namespace = sh.name, s.ns
		nl.Metadata.Labels = map[string]string{s.keys.leaseGroup: s.group, s.keys.leaseRole: "shard"}
		nl.Spec.HolderIdentity = s.identity
		nl.Spec.LeaseDurationSeconds = int32(leaseDuration / time.Second)
		nl.Spec.AcquireTime, nl.Spec.RenewTime = stamp, stamp
		err = s.m.client.Create(ctx, client.Path("coordination.k8s.io/v1", "leases", s.ns, ""), nl, nil)
	} else {
		nl := *l
		nl.Metadata.Labels = map[string]string{s.keys.leaseGroup: s.group, s.keys.leaseRole: "shard"}
		if nl.Spec.HolderIdentity != s.identity {
			nl.Spec.LeaseTransitions++
			nl.Spec.AcquireTime = stamp
		}
		nl.Spec.HolderIdentity = s.identity
		nl.Spec.LeaseDurationSeconds = int32(leaseDuration / time.Second)
		nl.Spec.RenewTime = stamp
		err = s.m.client.Update(ctx, s.leasePath(sh.name), nl, nil)
	}
	if err != nil && !client.IsConflict(err) && !client.IsAlreadyExists(err) {
		s.log.Warn("writing shard lease failed", "shard", sh.name, "err", err)
	}
	return err == nil
}

// release gives up sh's lease l so that another replica can take it at
// once, instead of after it expires.
func (s *sharder) release(ctx context.Context, sh *shard, l *lease) {
	if l == nil || l.Spec.HolderIdentity != s.identity {
		return
	}
	nl := *l
	nl.Spec.HolderIdentity = ""
	nl.Spec.LeaseDurationSeconds = 1
	nl.Spec.RenewTime = time.Now().UTC().Format(microTime)
	if err := s.m.client.Update(ctx, s.leasePath(sh.name), nl, nil); err != nil {
		s.log.Warn("releasing shard lease failed; it expires on its own", "shard", sh.name, "err", err)
		return
	}
	s.log.Info("released shard", "shard", sh.name)
}

// releaseAll releases every shard this replica holds and its membership,
// when it stops, so other replicas take over at once.
func (s *sharder) releaseAll() {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	s.mu.Lock()
	var held []*shard
	for _, sh := range s.shards {
		if sh.held {
			held = append(held, sh)
			sh.held = false
		}
	}
	member := s.member
	s.mu.Unlock()
	for _, sh := range held {
		var l lease
		if err := s.m.client.Get(ctx, s.leasePath(sh.name), &l); err == nil {
			s.release(ctx, sh, &l)
		}
	}
	if member != nil {
		_ = s.m.client.Delete(ctx, s.leasePath(member.Metadata.Name), client.DeleteOptions{})
	}
}

func (s *sharder) memberName() string {
	h := fnv.New64a()
	h.Write([]byte(s.identity))
	return s.group + "-member-" + strconv.FormatUint(h.Sum64(), 36)
}

// renewMembership creates or renews this replica's membership Lease.
func (s *sharder) renewMembership(ctx context.Context, now time.Time) {
	s.mu.Lock()
	prev := s.member
	s.mu.Unlock()
	stamp := now.UTC().Format(microTime)
	var l lease
	if prev != nil {
		l = *prev
	} else {
		l.APIVersion, l.Kind = "coordination.k8s.io/v1", "Lease"
		l.Metadata.Name, l.Metadata.Namespace = s.memberName(), s.ns
		l.Metadata.Labels = map[string]string{s.keys.leaseGroup: s.group, s.keys.leaseRole: "member"}
		l.Spec.HolderIdentity = s.identity
		l.Spec.LeaseDurationSeconds = int32(leaseDuration / time.Second)
		l.Spec.AcquireTime = stamp
	}
	l.Spec.RenewTime = stamp
	var out lease
	var err error
	if prev == nil {
		err = s.m.client.Create(ctx, client.Path("coordination.k8s.io/v1", "leases", s.ns, ""), l, &out)
		if client.IsAlreadyExists(err) {
			err = s.m.client.Get(ctx, s.leasePath(l.Metadata.Name), &out)
		}
	} else {
		err = s.m.client.Update(ctx, s.leasePath(l.Metadata.Name), l, &out)
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	switch {
	case err == nil:
		s.member = &out
	case client.IsConflict(err) || client.IsNotFound(err):
		s.member = nil
	default:
		s.log.Warn("renewing membership failed", "err", err)
	}
}

// liveMembers returns the identities of replicas whose membership Leases
// are current, including this replica, sorted. It deletes membership Leases
// that stopped being renewed long ago.
func (s *sharder) liveMembers(ctx context.Context, leases map[string]*lease, now time.Time) []string {
	live := []string{s.identity}
	if s.n == 1 {
		return live
	}
	s.mu.Lock()
	seen := map[string]bool{}
	var stale []*lease
	for name, l := range leases {
		if l.Metadata.Labels[s.keys.leaseRole] != "member" {
			continue
		}
		seen[name] = true
		o := s.members[name]
		if o == nil {
			o = &observation{}
			s.members[name] = o
		}
		switch {
		case l.Spec.HolderIdentity == s.identity:
		case !o.expired(l, now):
			live = append(live, l.Spec.HolderIdentity)
		case now.Sub(o.at) > memberExpiry:
			stale = append(stale, l)
		}
	}
	for name := range s.members {
		if !seen[name] {
			delete(s.members, name)
		}
	}
	s.mu.Unlock()
	for _, l := range stale {
		if err := s.m.client.Delete(ctx, s.leasePath(l.Metadata.Name), client.DeleteOptions{UID: l.Metadata.UID}); err == nil {
			s.log.Info("deleted the membership of a replica that stopped", "member", l.Spec.HolderIdentity)
		}
	}
	slices.Sort(live)
	return slices.Compact(live)
}

// rendezvous returns the member that shard i is assigned to: the one with
// the highest hash of its identity and the shard. Every replica computes the
// same answer from the same members, and a member coming or going moves only
// the shards assigned to it.
func rendezvous(members []string, i int) string {
	var best string
	var bestScore uint64
	for _, m := range members {
		h := fnv.New64a()
		h.Write([]byte(m))
		h.Write([]byte{'/'})
		h.Write([]byte(strconv.Itoa(i)))
		if score := mix(h.Sum64()); best == "" || score > bestScore || score == bestScore && m < best {
			best, bestScore = m, score
		}
	}
	return best
}

// mix is MurmurHash3's 64-bit finalizer. FNV-1a alone barely changes its
// high bits for the last bytes hashed, which would give every shard to the
// same member.
func mix(h uint64) uint64 {
	h ^= h >> 33
	h *= 0xff51afd7ed558ccd
	h ^= h >> 33
	h *= 0xc4ceb9fe1a85ec53
	h ^= h >> 33
	return h
}
