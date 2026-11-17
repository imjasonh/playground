package actorpool_test

import (
	"context"
	"errors"
	"fmt"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/ci-substrate/internal/actorpool"
)

const (
	basePool  = "ci-substrate-workers/ci-runner-base"
	burstPool = "ci-substrate-workers/ci-runner"
)

// fakeSubstrate records the pool's calls and moves actors between states
// the way Substrate would, one step per call. With workers set, a resume
// places the actor on a base worker, then on a ready burst worker, and fails
// when neither has room.
type fakeSubstrate struct {
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
	var out []actorpool.Actor
	for name, st := range f.actors {
		out = append(out, actorpool.Actor{Name: name, State: st, WorkerPool: f.placed[name]})
	}
	return out, nil
}

func (f *fakeSubstrate) op(verb, name string, to actorpool.State) error {
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

// fakeWorkers is the burst WorkerPool. Its workers take room only once a
// test marks them ready.
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
	calls := f.calls
	f.calls = nil
	slices.Sort(calls)
	return calls
}

type fakeQueue struct {
	queued int
	busy   []string
}

func (q *fakeQueue) Status(context.Context) (int, []string, error) {
	return q.queued, q.busy, nil
}

type harness struct {
	sub     *fakeSubstrate
	queue   *fakeQueue
	workers *fakeWorkers
	pool    *actorpool.Pool
	now     time.Time
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
	})
	if err != nil {
		t.Fatal(err)
	}
	h.pool = p
	return h
}

// newScalingHarness is newHarness with a pool that sizes the burst
// WorkerPool on top of baseSlots that always have room.
func newScalingHarness(t *testing.T, warm, maxActors, baseSlots, perWorker, maxWorkers int) *harness {
	t.Helper()
	h := &harness{sub: newFake(), queue: &fakeQueue{}, now: time.Unix(1_700_000_000, 0)}
	h.workers = &fakeWorkers{sub: h.sub, baseSlots: baseSlots, perWorker: perWorker, fail: map[string]error{}}
	h.sub.workers = h.workers
	p, err := actorpool.New(actorpool.Config{
		Actors:          h.sub,
		Queue:           h.queue,
		Prefix:          "ci-runner-",
		Warm:            warm,
		Max:             maxActors,
		IdleAfter:       time.Minute,
		Now:             func() time.Time { return h.now },
		Workers:         h.workers,
		WorkerPool:      burstPool,
		BaseSlots:       baseSlots,
		ActorsPerWorker: perWorker,
		MaxWorkers:      maxWorkers,
	})
	if err != nil {
		t.Fatal(err)
	}
	h.pool = p
	return h
}

// reconcileErr reconciles once, expecting an error, and returns the calls.
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
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Workers: &fakeWorkers{}, ActorsPerWorker: 1, MaxWorkers: 1},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Workers: &fakeWorkers{}, WorkerPool: burstPool, MaxWorkers: 1},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Workers: &fakeWorkers{}, WorkerPool: burstPool, ActorsPerWorker: 1},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 1, Workers: &fakeWorkers{}, WorkerPool: burstPool, ActorsPerWorker: 1, MaxWorkers: 1, BaseSlots: -1},
	} {
		if _, err := actorpool.New(cfg); err == nil {
			t.Errorf("New(%+v) succeeded", cfg)
		}
	}
}

func TestScalesWorkersForWorkBeyondBaseThenToZero(t *testing.T) {
	h := newScalingHarness(t, 1, 4, 1, 1, 3)
	// The warm actor fits on the base worker: no burst worker starts.
	if got := h.reconcile(t); !slices.Equal(got, []string{"create ci-runner-0", "resume ci-runner-0"}) {
		t.Fatalf("prewarm %v", got)
	}
	// It is busy and two more jobs queue. The pool asks for two burst
	// workers before it resumes the new actors, which find no room while
	// those workers start.
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
	// Work drains. The workers stay while the runners idle out, then go
	// to zero once every actor on them is suspended.
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
	// Two warm actors: one fits on the base worker, and the other waits for
	// a burst worker.
	if got := h.reconcileErr(t); !slices.Equal(got, []string{"create ci-runner-0", "create ci-runner-1", "resume ci-runner-0", "resume ci-runner-1", "scale 1"}) {
		t.Fatalf("prewarm %v", got)
	}
	// Nothing is queued, but ci-runner-1 has no snapshot yet. The pool keeps
	// its worker and resumes it until the worker is up.
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
	// Both idle out, leaving two snapshots and no burst worker.
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
	// The burst worker is empty, but a job arrives in the same reconcile:
	// the pool resumes for it and leaves the workers alone.
	h.sub.actors["ci-runner-1"] = actorpool.StateSuspended
	delete(h.sub.placed, "ci-runner-1")
	h.queue.queued = 1
	if got := h.reconcile(t); !slices.Equal(got, []string{"resume ci-runner-0"}) {
		t.Fatalf("waking %v", got)
	}
	if got := h.sub.placed["ci-runner-0"]; got != basePool {
		t.Fatalf("resumed on %q, want the base pool", got)
	}
	// With the job leased on the base worker, the burst workers go.
	h.queue.queued, h.queue.busy = 0, []string{"ci-runner-0"}
	if got := h.reconcile(t); !slices.Equal(got, []string{"scale 0"}) {
		t.Fatalf("empty burst %v", got)
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
	// Two workers hold four actors. The other five keep failing to
	// resume, and the pool asks for no more workers.
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
