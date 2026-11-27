package actorpool_test

import (
	"context"
	"errors"
	"fmt"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/imjasonh/playground/ci-substrate/internal/actorpool"
)

const (
	basePool  = "ci-substrate-workers/ci-runner-base"
	burstPool = "ci-substrate-workers/ci-runner"
)

// fakeSubstrate records the pool's calls and moves actors between states
// the way Substrate would, one step per call.
type fakeSubstrate struct {
	mu      sync.Mutex
	actors  map[string]actorpool.State
	placed  map[string]string
	calls   []string
	fail    map[string]error
	workers *fakeWorkers
}

func newFake() *fakeSubstrate {
	return &fakeSubstrate{actors: map[string]actorpool.State{}, placed: map[string]string{}, fail: map[string]error{}}
}

func (f *fakeSubstrate) List(context.Context) ([]actorpool.Actor, error) {
	f.mu.Lock()
	defer f.mu.Unlock()
	var out []actorpool.Actor
	for name, st := range f.actors {
		out = append(out, actorpool.Actor{Name: name, State: st, WorkerPool: f.placed[name]})
	}
	return out, nil
}

func (f *fakeSubstrate) op(verb, name string, to actorpool.State) error {
	f.mu.Lock()
	defer f.mu.Unlock()
	f.calls = append(f.calls, verb+" "+name)
	if err := f.fail[verb]; err != nil {
		return err
	}
	if to == actorpool.StateRunning && f.workers != nil {
		pool, err := f.place()
		if err != nil {
			return err
		}
		f.placed[name] = pool
	}
	if to != actorpool.StateRunning {
		delete(f.placed, name)
	}
	if to == actorpool.StateUnknown {
		delete(f.actors, name)
	} else {
		f.actors[name] = to
	}
	return nil
}

func (f *fakeSubstrate) place() (string, error) {
	on := map[string]int{}
	for _, pool := range f.placed {
		on[pool]++
	}
	switch {
	case on[basePool] < f.workers.baseSlots:
		return basePool, nil
	case on[burstPool] < f.workers.ready*f.workers.perWorker:
		return burstPool, nil
	default:
		return "", errors.New("no worker has room for the actor")
	}
}

type fakeWorkers struct {
	sub                  *fakeSubstrate
	baseSlots, perWorker int
	replicas, ready      int
	fail                 map[string]error
}

func (w *fakeWorkers) Replicas(context.Context) (int, error) {
	if err := w.fail["replicas"]; err != nil {
		return 0, err
	}
	return w.replicas, nil
}

func (w *fakeWorkers) Scale(_ context.Context, n int) error {
	w.sub.calls = append(w.sub.calls, fmt.Sprintf("scale %d", n))
	if err := w.fail["scale"]; err != nil {
		return err
	}
	w.replicas = n
	w.ready = min(w.ready, n)
	return nil
}

func (f *fakeSubstrate) Create(_ context.Context, name string) error {
	return f.op("create", name, actorpool.StateSuspended)
}

func (f *fakeSubstrate) CreateFromTag(_ context.Context, name, tag string) error {
	return f.op("create-from-tag:"+tag, name, actorpool.StateSuspended)
}

func (f *fakeSubstrate) Resume(_ context.Context, name string) error {
	return f.op("resume", name, actorpool.StateRunning)
}

func (f *fakeSubstrate) Suspend(_ context.Context, name string) error {
	return f.op("suspend", name, actorpool.StateSuspended)
}

func (f *fakeSubstrate) Delete(_ context.Context, name string) error {
	return f.op("delete", name, actorpool.StateUnknown)
}

func (f *fakeSubstrate) take() []string {
	f.mu.Lock()
	defer f.mu.Unlock()
	calls := f.calls
	f.calls = nil
	slices.Sort(calls)
	return calls
}

// fakeQueue reports queued and busy. Its Watch calls changed once for each
// value sent on changes, and fails instead while watchErr is set.
type fakeQueue struct {
	mu               sync.Mutex
	queued           int
	queuedByPlatform map[string]int
	busy             []string
	statuses         int
	watches          int
	watchErr         error
	changes          chan struct{}
}

func (q *fakeQueue) Status(context.Context) (int, []string, error) {
	q.mu.Lock()
	defer q.mu.Unlock()
	q.statuses++
	return q.queued, q.busy, nil
}

func (q *fakeQueue) StatusByPlatform(context.Context) (map[string]int, []string, error) {
	q.mu.Lock()
	defer q.mu.Unlock()
	q.statuses++
	out := map[string]int{"": q.queued}
	for k, v := range q.queuedByPlatform {
		out[k] = v
	}
	return out, q.busy, nil
}

func (q *fakeQueue) Watch(ctx context.Context, changed func()) error {
	q.mu.Lock()
	q.watches++
	err := q.watchErr
	q.mu.Unlock()
	if err != nil {
		return err
	}
	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-q.changes:
			changed()
		}
	}
}

// eventually fails t unless cond becomes true within a few seconds.
func eventually(t *testing.T, what string, cond func() bool) {
	t.Helper()
	for deadline := time.Now().Add(5 * time.Second); !cond(); {
		if time.Now().After(deadline) {
			t.Fatalf("timed out waiting for %s", what)
		}
		time.Sleep(5 * time.Millisecond)
	}
}

// runPool runs p until the test ends.
func runPool(t *testing.T, p *actorpool.Pool) {
	t.Helper()
	ctx, cancel := context.WithCancel(t.Context())
	done := make(chan error)
	go func() { done <- p.Run(ctx) }()
	t.Cleanup(func() {
		cancel()
		if err := <-done; !errors.Is(err, context.Canceled) {
			t.Errorf("Run returned %v", err)
		}
	})
}

// A queued job wakes an actor as soon as the scheduler reports it, long
// before Run's next tick.
func TestRunReconcilesWhenQueueChanges(t *testing.T) {
	sub := newFake()
	sub.actors["ci-runner-0"] = actorpool.StateSuspended
	queue := &fakeQueue{changes: make(chan struct{})}
	p, err := actorpool.New(actorpool.Config{Actors: sub, Queue: queue, Prefix: "ci-runner-", Warm: 1, Max: 1, Interval: time.Hour})
	if err != nil {
		t.Fatal(err)
	}
	runPool(t, p)
	eventually(t, "the first reconcile", func() bool {
		queue.mu.Lock()
		defer queue.mu.Unlock()
		return queue.statuses == 1
	})
	if got := sub.take(); len(got) != 0 {
		t.Fatalf("first reconcile %v", got)
	}

	queue.mu.Lock()
	queue.queued = 1
	queue.mu.Unlock()
	queue.changes <- struct{}{}
	eventually(t, "the resume", func() bool {
		sub.mu.Lock()
		defer sub.mu.Unlock()
		return slices.Equal(sub.calls, []string{"resume ci-runner-0"})
	})
}

// A watch that fails is opened again, and Run keeps reconciling meanwhile.
func TestRunReopensBrokenWatch(t *testing.T) {
	queue := &fakeQueue{watchErr: errors.New("cas restarting")}
	p, err := actorpool.New(actorpool.Config{Actors: newFake(), Queue: queue, Prefix: "ci-runner-", Max: 1, Interval: 10 * time.Millisecond})
	if err != nil {
		t.Fatal(err)
	}
	runPool(t, p)
	eventually(t, "a second watch and reconciles on the ticker", func() bool {
		queue.mu.Lock()
		defer queue.mu.Unlock()
		return queue.watches >= 2 && queue.statuses >= 2
	})
}

type harness struct {
	sub     *fakeSubstrate
	queue   *fakeQueue
	workers *fakeWorkers
	pool    *actorpool.Pool
	now     time.Time
}

func sequentialName(prefix string) func() string {
	next := 0
	return func() string {
		name := fmt.Sprintf("%s%d", prefix, next)
		next++
		return name
	}
}

func newHarness(t *testing.T, warm, maxActors int) *harness {
	t.Helper()
	h := &harness{sub: newFake(), queue: &fakeQueue{}, now: time.Unix(1_700_000_000, 0)}
	p, err := actorpool.New(actorpool.Config{
		Actors:    h.sub,
		Queue:     h.queue,
		Prefix:    "ci-runner-",
		Warm:      warm,
		Max:       maxActors,
		IdleAfter: time.Minute,
		Now:       func() time.Time { return h.now },
		NewName:   sequentialName("ci-runner-"),
	})
	if err != nil {
		t.Fatal(err)
	}
	h.pool = p
	return h
}

func newScalingHarness(t *testing.T, warm, maxActors, baseSlots, perWorker, maxWorkers int) *harness {
	t.Helper()
	h := &harness{sub: newFake(), queue: &fakeQueue{}, now: time.Unix(1_700_000_000, 0)}
	h.workers = &fakeWorkers{sub: h.sub, baseSlots: baseSlots, perWorker: perWorker, fail: map[string]error{}}
	h.sub.workers = h.workers
	p, err := actorpool.New(actorpool.Config{
		Actors:    h.sub,
		Queue:     h.queue,
		Prefix:    "ci-runner-",
		Warm:      warm,
		Max:       maxActors,
		IdleAfter: time.Minute,
		Now:       func() time.Time { return h.now },
		NewName:   sequentialName("ci-runner-"),
		Burst: &actorpool.Burst{
			Workers:         h.workers,
			Name:            burstPool,
			BaseSlots:       baseSlots,
			ActorsPerWorker: perWorker,
			MaxWorkers:      maxWorkers,
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	h.pool = p
	return h
}

func (h *harness) reconcileErr(t *testing.T) []string {
	t.Helper()
	if err := h.pool.Reconcile(t.Context()); err == nil {
		t.Fatal("Reconcile succeeded, want an error")
	}
	return h.sub.take()
}

func (h *harness) reconcile(t *testing.T) []string {
	t.Helper()
	if err := h.pool.Reconcile(t.Context()); err != nil {
		t.Fatal(err)
	}
	return h.sub.take()
}

func (h *harness) states() string {
	var parts []string
	for name, st := range h.sub.actors {
		parts = append(parts, name+"="+st.String())
	}
	slices.Sort(parts)
	return strings.Join(parts, " ")
}

func TestPrewarmsThenSuspendsIdle(t *testing.T) {
	h := newHarness(t, 2, 4)
	// An empty pool creates Warm actors and runs each once.
	if got := h.reconcile(t); !slices.Equal(got, []string{"create ci-runner-0", "create ci-runner-1", "resume ci-runner-0", "resume ci-runner-1"}) {
		t.Fatalf("first reconcile %v", got)
	}
	// They are running and idle, but inside IdleAfter: nothing happens.
	h.now = h.now.Add(30 * time.Second)
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("within IdleAfter %v", got)
	}
	// Past IdleAfter with nothing queued, both are suspended: the pool is
	// now Warm suspended actors, each with a snapshot.
	h.now = h.now.Add(31 * time.Second)
	if got := h.reconcile(t); !slices.Equal(got, []string{"suspend ci-runner-0", "suspend ci-runner-1"}) {
		t.Fatalf("past IdleAfter %v", got)
	}
	if got := h.states(); got != "ci-runner-0=suspended ci-runner-1=suspended" {
		t.Fatalf("states %q", got)
	}
	// Steady state is quiet.
	h.now = h.now.Add(time.Hour)
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("steady state %v", got)
	}
}

func TestResumesForQueuedWorkAndBurstsToMax(t *testing.T) {
	h := newHarness(t, 2, 3)
	h.sub.actors["ci-runner-0"] = actorpool.StateSuspended
	h.sub.actors["ci-runner-1"] = actorpool.StateSuspended
	h.sub.actors["other-actor"] = actorpool.StateSuspended

	// One queued job wakes one suspended actor, lowest name first, and
	// leaves the actor without the prefix alone.
	h.queue.queued = 1
	if got := h.reconcile(t); !slices.Equal(got, []string{"resume ci-runner-0"}) {
		t.Fatalf("one queued %v", got)
	}
	// It leases the job. Two more queued: the second suspended actor
	// resumes, and a third is created up to Max; the fourth waits.
	h.queue.busy = []string{"ci-runner-0"}
	h.queue.queued = 3
	if got := h.reconcile(t); !slices.Equal(got, []string{"create ci-runner-2", "resume ci-runner-1", "resume ci-runner-2"}) {
		t.Fatalf("burst %v", got)
	}
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("at Max %v", got)
	}
	// Work drains. The runners idle out, and the surplus actor over Warm is
	// deleted once suspended.
	h.queue.busy, h.queue.queued = nil, 0
	h.now = h.now.Add(2 * time.Minute)
	if got := h.reconcile(t); !slices.Equal(got, []string{"suspend ci-runner-0", "suspend ci-runner-1", "suspend ci-runner-2"}) {
		t.Fatalf("drain %v", got)
	}
	if got := h.reconcile(t); !slices.Equal(got, []string{"delete ci-runner-2"}) {
		t.Fatalf("surplus %v", got)
	}
	if got := h.states(); got != "ci-runner-0=suspended ci-runner-1=suspended other-actor=suspended" {
		t.Fatalf("states %q", got)
	}
}

func TestBusyRunnerIsNotSuspended(t *testing.T) {
	h := newHarness(t, 1, 2)
	h.sub.actors["ci-runner-0"] = actorpool.StateRunning
	h.queue.busy = []string{"ci-runner-0"}
	h.reconcile(t)
	// A long action keeps the runner busy well past IdleAfter.
	h.now = h.now.Add(time.Hour)
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("busy runner touched: %v", got)
	}
	// Once its lease ends, the idle clock starts from then.
	h.queue.busy = nil
	h.now = h.now.Add(30 * time.Second)
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("just idle: %v", got)
	}
	h.now = h.now.Add(31 * time.Second)
	if got := h.reconcile(t); !slices.Equal(got, []string{"suspend ci-runner-0"}) {
		t.Fatalf("idle: %v", got)
	}
}

func TestIdleRunnerIsKeptForQueuedWork(t *testing.T) {
	h := newHarness(t, 1, 2)
	h.sub.actors["ci-runner-0"] = actorpool.StateRunning
	h.reconcile(t)
	h.now = h.now.Add(2 * time.Minute)
	// A job is queued; the idle runner is about to lease it, so it stays.
	h.queue.queued = 1
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("idle runner with queued work: %v", got)
	}
}

func TestReplacesCrashedActor(t *testing.T) {
	h := newHarness(t, 1, 2)
	h.sub.actors["ci-runner-0"] = actorpool.StateCrashed
	// The replacement takes a fresh name: the deletion may still be in
	// progress on Substrate's side.
	if got := h.reconcile(t); !slices.Equal(got, []string{"create ci-runner-1", "delete ci-runner-0", "resume ci-runner-1"}) {
		t.Fatalf("crashed %v", got)
	}
}

func TestReportsErrorsAndKeepsGoing(t *testing.T) {
	h := newHarness(t, 2, 2)
	boom := errors.New("api down")
	h.sub.fail["resume"] = boom
	err := h.pool.Reconcile(t.Context())
	if !errors.Is(err, boom) {
		t.Fatalf("err %v, want %v", err, boom)
	}
	// Both actors were created even though neither resumed.
	if got := h.sub.take(); !slices.Equal(got, []string{"create ci-runner-0", "create ci-runner-1", "resume ci-runner-0", "resume ci-runner-1"}) {
		t.Fatalf("calls %v", got)
	}
	// With no queued work, the pool still resumes them, because neither has
	// the snapshot a warm actor needs.
	delete(h.sub.fail, "resume")
	if got := h.reconcile(t); !slices.Equal(got, []string{"resume ci-runner-0", "resume ci-runner-1"}) {
		t.Fatalf("retry %v", got)
	}
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("steady state %v", got)
	}
}

func TestFullWorkersDoNotCascadeIntoCreates(t *testing.T) {
	h := newHarness(t, 1, 4)
	h.reconcile(t)
	h.sub.actors["ci-runner-0"] = actorpool.StateSuspended
	h.sub.take()

	// One queued job and a worker pool with no room: the pool tries the
	// warm actor and stops. It does not create actors that would not resume
	// either.
	h.queue.queued = 1
	h.sub.fail["resume"] = errors.New("no worker has room for the actor")
	if err := h.pool.Reconcile(t.Context()); err == nil {
		t.Fatal("resume failure not reported")
	}
	if got := h.sub.take(); !slices.Equal(got, []string{"resume ci-runner-0"}) {
		t.Fatalf("calls %v", got)
	}
	delete(h.sub.fail, "resume")
	if got := h.reconcile(t); !slices.Equal(got, []string{"resume ci-runner-0"}) {
		t.Fatalf("retry %v", got)
	}
}

func TestRejectsBadConfig(t *testing.T) {
	for _, cfg := range []actorpool.Config{
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "", Max: 1},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Warm: 2, Max: 1},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 0},
		{Queue: &fakeQueue{}, Prefix: "p-", Max: 1},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Burst: &actorpool.Burst{Name: burstPool, ActorsPerWorker: 1, MaxWorkers: 1}},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Burst: &actorpool.Burst{Workers: &fakeWorkers{}, ActorsPerWorker: 1, MaxWorkers: 1}},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Burst: &actorpool.Burst{Workers: &fakeWorkers{}, Name: burstPool, MaxWorkers: 1}},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Burst: &actorpool.Burst{Workers: &fakeWorkers{}, Name: burstPool, ActorsPerWorker: 1}},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Burst: &actorpool.Burst{Workers: &fakeWorkers{}, Name: burstPool, ActorsPerWorker: 1, MaxWorkers: 1, BaseSlots: -1}},
	} {
		if _, err := actorpool.New(cfg); err == nil {
			t.Errorf("New(%+v) succeeded", cfg)
		}
	}
}

func TestScalesWorkersForWorkBeyondBaseThenToZero(t *testing.T) {
	h := newScalingHarness(t, 1, 4, 1, 1, 3)
	if got := h.reconcile(t); !slices.Equal(got, []string{"create ci-runner-0", "resume ci-runner-0"}) {
		t.Fatalf("prewarm %v", got)
	}
	h.queue.busy, h.queue.queued = []string{"ci-runner-0"}, 2
	if got := h.reconcileErr(t); !slices.Equal(got, []string{"create ci-runner-1", "create ci-runner-2", "resume ci-runner-1", "resume ci-runner-2", "scale 2"}) {
		t.Fatalf("burst %v", got)
	}
	// Until the workers are ready, the pool retries the same resumes and
	// neither creates more actors nor asks for more workers.
	if got := h.reconcileErr(t); !slices.Equal(got, []string{"resume ci-runner-1", "resume ci-runner-2"}) {
		t.Fatalf("starting workers %v", got)
	}
	h.workers.ready = 2
	if got := h.reconcile(t); !slices.Equal(got, []string{"resume ci-runner-1", "resume ci-runner-2"}) {
		t.Fatalf("workers ready %v", got)
	}
	if got := h.states(); got != "ci-runner-0=running ci-runner-1=running ci-runner-2=running" {
		t.Fatalf("states %q", got)
	}
	h.queue.busy, h.queue.queued = nil, 0
	h.now = h.now.Add(2 * time.Minute)
	if got := h.reconcile(t); !slices.Equal(got, []string{"suspend ci-runner-0", "suspend ci-runner-1", "suspend ci-runner-2"}) {
		t.Fatalf("drain %v", got)
	}
	if got := h.reconcile(t); !slices.Equal(got, []string{"delete ci-runner-1", "delete ci-runner-2", "scale 0"}) {
		t.Fatalf("scale down %v", got)
	}
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("steady state %v", got)
	}
}

func TestKeepsWorkersForWarmActorsThatHaveNotRun(t *testing.T) {
	h := newScalingHarness(t, 2, 4, 1, 1, 2)
	if got := h.reconcileErr(t); !slices.Equal(got, []string{"create ci-runner-0", "create ci-runner-1", "resume ci-runner-0", "resume ci-runner-1", "scale 1"}) {
		t.Fatalf("prewarm %v", got)
	}
	if got := h.reconcileErr(t); !slices.Equal(got, []string{"resume ci-runner-1"}) {
		t.Fatalf("starting worker %v", got)
	}
	h.workers.ready = 1
	if got := h.reconcile(t); !slices.Equal(got, []string{"resume ci-runner-1"}) {
		t.Fatalf("worker ready %v", got)
	}
	if got := h.sub.placed["ci-runner-1"]; got != burstPool {
		t.Fatalf("resumed on %q, want the burst pool", got)
	}
	h.now = h.now.Add(2 * time.Minute)
	if got := h.reconcile(t); !slices.Equal(got, []string{"suspend ci-runner-0", "suspend ci-runner-1"}) {
		t.Fatalf("idle %v", got)
	}
	if got := h.reconcile(t); !slices.Equal(got, []string{"scale 0"}) {
		t.Fatalf("scale down %v", got)
	}
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("steady state %v", got)
	}
}

func TestKeepsWorkersWhileTheyHostActors(t *testing.T) {
	h := newScalingHarness(t, 2, 4, 1, 1, 2)
	h.workers.replicas, h.workers.ready = 2, 2
	h.sub.actors["ci-runner-0"] = actorpool.StateRunning
	h.sub.placed["ci-runner-0"] = basePool
	h.sub.actors["ci-runner-1"] = actorpool.StateRunning
	h.sub.placed["ci-runner-1"] = burstPool
	h.queue.busy = []string{"ci-runner-1"}
	// One burst worker would do, but Kubernetes might stop the one that
	// hosts the busy actor.
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("busy burst actor %v", got)
	}
	h.now = h.now.Add(2 * time.Minute)
	if got := h.reconcile(t); !slices.Equal(got, []string{"suspend ci-runner-0"}) {
		t.Fatalf("idle base actor %v", got)
	}
	// Its worker is writing the snapshot.
	h.queue.busy = nil
	h.sub.actors["ci-runner-1"] = actorpool.StateSuspending
	if got := h.reconcile(t); len(got) != 0 {
		t.Fatalf("suspending burst actor %v", got)
	}
	h.sub.actors["ci-runner-1"] = actorpool.StateSuspended
	delete(h.sub.placed, "ci-runner-1")
	h.queue.queued = 1
	if got := h.reconcile(t); !slices.Equal(got, []string{"resume ci-runner-0"}) {
		t.Fatalf("waking %v", got)
	}
	if got := h.sub.placed["ci-runner-0"]; got != basePool {
		t.Fatalf("resumed on %q, want the base pool", got)
	}
	h.queue.queued, h.queue.busy = 0, []string{"ci-runner-0"}
	if got := h.reconcile(t); !slices.Equal(got, []string{"scale 0"}) {
		t.Fatalf("empty burst %v", got)
	}
}

func TestDoesNotFlapWhenBaseHoldsMoreThanBaseSlots(t *testing.T) {
	h := newScalingHarness(t, 0, 4, 1, 1, 2)
	h.workers.baseSlots = 2
	h.workers.replicas, h.workers.ready = 1, 1
	for _, name := range []string{"ci-runner-0", "ci-runner-1"} {
		h.sub.actors[name] = actorpool.StateRunning
		h.sub.placed[name] = basePool
	}
	h.queue.busy = []string{"ci-runner-0", "ci-runner-1"}
	// The burst worker hosts nothing, but BaseSlots says the second actor
	// needs it. Scaling it to zero would scale it back up next time.
	for range 3 {
		if got := h.reconcile(t); len(got) != 0 {
			t.Fatalf("calls %v", got)
		}
	}
}

func TestWorkersStopAtMaxWorkers(t *testing.T) {
	h := newScalingHarness(t, 0, 10, 0, 2, 2)
	h.queue.queued = 9
	got := h.reconcileErr(t)
	if !slices.Contains(got, "scale 2") {
		t.Fatalf("calls %v, want scale 2", got)
	}
	if creates := len(slices.DeleteFunc(got, func(c string) bool { return !strings.HasPrefix(c, "create ") })); creates != 9 {
		t.Fatalf("%d creates, want 9", creates)
	}
	h.workers.ready = 2
	got = h.reconcileErr(t)
	if slices.ContainsFunc(got, func(c string) bool { return strings.HasPrefix(c, "scale ") }) {
		t.Fatalf("scaled past MaxWorkers: %v", got)
	}
	if got := strings.Count(h.states(), "running"); got != 4 {
		t.Fatalf("%d running, want 4: %s", got, h.states())
	}
}

func TestWorkerErrorsDoNotStopActors(t *testing.T) {
	h := newScalingHarness(t, 1, 2, 1, 1, 2)
	boom := errors.New("apiserver down")
	h.workers.fail["replicas"] = boom
	if err := h.pool.Reconcile(t.Context()); !errors.Is(err, boom) {
		t.Fatalf("err %v, want %v", err, boom)
	}
	if got := h.sub.take(); !slices.Equal(got, []string{"create ci-runner-0", "resume ci-runner-0"}) {
		t.Fatalf("calls %v", got)
	}
	delete(h.workers.fail, "replicas")
	h.workers.fail["scale"] = boom
	h.queue.busy, h.queue.queued = []string{"ci-runner-0"}, 1
	if err := h.pool.Reconcile(t.Context()); !errors.Is(err, boom) {
		t.Fatalf("err %v, want %v", err, boom)
	}
	if got := h.sub.take(); !slices.Equal(got, []string{"create ci-runner-1", "resume ci-runner-1", "scale 1"}) {
		t.Fatalf("calls %v", got)
	}
	if h.workers.replicas != 0 {
		t.Fatalf("replicas %d after a failed scale", h.workers.replicas)
	}
}

func TestDefaultActorNamesAreUniqueAndNotReused(t *testing.T) {
	sub := newFake()
	queue := &fakeQueue{}
	p, err := actorpool.New(actorpool.Config{
		Actors:    sub,
		Queue:     queue,
		Prefix:    "ci-runner-",
		Warm:      1,
		Max:       2,
		IdleAfter: time.Minute,
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := p.Reconcile(t.Context()); err != nil {
		t.Fatal(err)
	}
	if len(sub.actors) != 1 {
		t.Fatalf("expected 1 actor, got %v", sub.actors)
	}
	var first string
	for name := range sub.actors {
		first = name
	}
	if !strings.HasPrefix(first, "ci-runner-") {
		t.Fatalf("name %q missing prefix", first)
	}
	if len(first) > 63 {
		t.Fatalf("name %q exceeds 63-char k8s-short-name limit (%d)", first, len(first))
	}
	for _, r := range first {
		if (r < 'a' || r > 'z') && (r < '0' || r > '9') && r != '-' {
			t.Fatalf("name %q contains invalid DNS label char %q", first, r)
		}
	}

	// Mark the first actor crashed and reconcile: it is deleted and replaced
	// with a fresh name, never reusing the deleted actor's name.
	sub.actors[first] = actorpool.StateCrashed
	if err := p.Reconcile(t.Context()); err != nil {
		t.Fatal(err)
	}
	if _, stillThere := sub.actors[first]; stillThere {
		t.Fatalf("crashed actor %q was not deleted", first)
	}
	if len(sub.actors) != 1 {
		t.Fatalf("expected 1 replacement actor, got %v", sub.actors)
	}
	for second := range sub.actors {
		if second == first {
			t.Fatalf("reused deleted actor name %q", first)
		}
		if !strings.HasPrefix(second, "ci-runner-") {
			t.Fatalf("replacement name %q missing prefix", second)
		}
	}
}

func TestForksActorsFromSourceTagForPlatformQueue(t *testing.T) {
	h := newHarness(t, 1, 4)
	h.sub.actors["ci-runner-0"] = actorpool.StateSuspended
	h.queue.queuedByPlatform = map[string]int{"env=warm-go": 1}

	calls := h.reconcile(t)
	var tagActor string
	for _, c := range calls {
		if after, ok := strings.CutPrefix(c, "create-from-tag:warm-go "); ok {
			tagActor = after
		}
	}
	if tagActor == "" {
		t.Fatalf("expected create-from-tag:warm-go call, got %v", calls)
	}
	if !strings.HasPrefix(tagActor, "ci-runner-env-warm-go--") {
		t.Fatalf("tag actor name = %q, want prefix ci-runner-env-warm-go--", tagActor)
	}
	if !slices.Contains(calls, "resume "+tagActor) {
		t.Fatalf("expected resume %s, got %v", tagActor, calls)
	}
	// Default warm actor stays untouched.
	if h.sub.actors["ci-runner-0"] != actorpool.StateSuspended {
		t.Fatalf("default warm actor state = %v, want suspended", h.sub.actors["ci-runner-0"])
	}

	// Once work drains and the tag actor idles out, it suspends and is deleted
	// (warm=0 for ad-hoc tag queues) while the default warm actor remains.
	h.queue.queuedByPlatform = nil
	h.now = h.now.Add(2 * time.Minute)
	if got := h.reconcile(t); !slices.Equal(got, []string{"suspend " + tagActor}) {
		t.Fatalf("idle tag actor = %v, want suspend", got)
	}
	if got := h.reconcile(t); !slices.Equal(got, []string{"delete " + tagActor}) {
		t.Fatalf("surplus tag actor = %v, want delete", got)
	}
	if h.states() != "ci-runner-0=suspended" {
		t.Fatalf("states = %q, want only default warm actor", h.states())
	}
}
