package actorpool_test

import (
	"context"
	"errors"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/imjasonh/playground/ci-substrate/internal/actorpool"
)

// fakeSubstrate records the pool's calls and moves actors between states
// the way Substrate would, one step per call.
type fakeSubstrate struct {
	actors map[string]actorpool.State
	calls  []string
	fail   map[string]error
}

func newFake() *fakeSubstrate {
	return &fakeSubstrate{actors: map[string]actorpool.State{}, fail: map[string]error{}}
}

func (f *fakeSubstrate) List(context.Context) ([]actorpool.Actor, error) {
	var out []actorpool.Actor
	for name, st := range f.actors {
		out = append(out, actorpool.Actor{Name: name, State: st})
	}
	return out, nil
}

func (f *fakeSubstrate) op(verb, name string, to actorpool.State) error {
	f.calls = append(f.calls, verb+" "+name)
	if err := f.fail[verb]; err != nil {
		return err
	}
	if to == actorpool.StateUnknown {
		delete(f.actors, name)
	} else {
		f.actors[name] = to
	}
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
	sub   *fakeSubstrate
	queue *fakeQueue
	pool  *actorpool.Pool
	now   time.Time
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
}

func TestRejectsBadConfig(t *testing.T) {
	for _, cfg := range []actorpool.Config{
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "", Max: 1},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Warm: 2, Max: 1},
		{Actors: newFake(), Queue: &fakeQueue{}, Prefix: "p-", Max: 0},
		{Queue: &fakeQueue{}, Prefix: "p-", Max: 1},
	} {
		if _, err := actorpool.New(cfg); err == nil {
			t.Errorf("New(%+v) succeeded", cfg)
		}
	}
}
