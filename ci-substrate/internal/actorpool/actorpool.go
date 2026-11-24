// Package actorpool keeps one tenant's Substrate runners sized to that
// tenant's queue. It owns the actors whose names carry its prefix, and each
// reconcile moves them along this lifecycle:
//
//   - A new actor is created and resumed, so that its first suspend leaves a
//     memory snapshot. Resuming from that snapshot is the warm path. A first
//     resume that fails is tried again on each reconcile until one succeeds.
//   - A queued job with no idle runner resumes a suspended actor, or creates
//     one when none is suspended and the pool is under its maximum.
//   - A running actor that has held no lease for IdleAfter is suspended.
//   - A suspended actor beyond Warm is deleted, and a crashed one is deleted
//     so the next reconcile replaces it.
//
// With Burst set, the pool also sizes a WorkerPool: enough workers for the
// actors that are awake or waking beyond BaseSlots, which fit on workers the
// pool does not size. It grows the WorkerPool before resuming actors that need
// it, and shrinks it, down to zero, once none of its actors is on one of
// those workers. A resume that finds no room fails and is tried again on the
// next reconcile, by which time the new worker may be up.
//
// The pool learns which actors are busy from the scheduler's Status, keyed by
// bot id, so the runner inside each actor reports the actor's name as its bot
// id. The pool never reads jobs or blobs: it sees counts and names.
package actorpool

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"slices"
	"strings"
	"sync"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"

	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
)

// State is the lifecycle state of an actor, as the pool sees it.
type State int

const (
	// StateUnknown is a state the pool does not act on, such as deleting
	// or reverting.
	StateUnknown State = iota
	// StateSuspended means the actor holds a snapshot and no worker.
	StateSuspended
	// StateResuming means a worker is restoring the actor.
	StateResuming
	// StateRunning means the actor's runner is leasing.
	StateRunning
	// StateSuspending means the actor is being checkpointed.
	StateSuspending
	// StateCrashed means the actor's workload failed.
	StateCrashed
)

// String names the state.
func (s State) String() string {
	switch s {
	case StateSuspended:
		return "suspended"
	case StateResuming:
		return "resuming"
	case StateRunning:
		return "running"
	case StateSuspending:
		return "suspending"
	case StateCrashed:
		return "crashed"
	default:
		return "unknown"
	}
}

// Actor is one actor the pool may own.
type Actor struct {
	Name  string
	State State
	// WorkerPool is the namespace/name of the WorkerPool whose worker hosts
	// the actor, or empty when no worker does.
	WorkerPool string
}

// Actors is the part of Substrate's control API the pool uses. Create makes
// a suspended actor from the pool's template with its egress policy; the
// pool resumes it afterwards.
type Actors interface {
	List(ctx context.Context) ([]Actor, error)
	Create(ctx context.Context, name string) error
	Resume(ctx context.Context, name string) error
	Suspend(ctx context.Context, name string) error
	Delete(ctx context.Context, name string) error
}

// Queue is the scheduler's view of the tenant: jobs waiting for a runner and
// the bot ids holding leases. Watch calls changed each time that view
// changes, until ctx ends or the watch breaks, and returns why it stopped.
type Queue interface {
	Status(ctx context.Context) (queued int, busy []string, err error)
	Watch(ctx context.Context, changed func()) error
}

// Workers is the WorkerPool the pool sizes: its desired number of workers,
// which Kubernetes then starts or stops.
type Workers interface {
	Replicas(ctx context.Context) (int, error)
	Scale(ctx context.Context, replicas int) error
}

// Config sizes a Pool.
type Config struct {
	Actors Actors
	Queue  Queue
	// Prefix starts the name of every actor the pool owns, such as
	// "ci-runner-". Other actors in the atespace are left alone.
	Prefix string
	// Warm is how many actors the pool keeps, suspended, when the queue is
	// empty. Each holds a snapshot, so a resume is warm.
	Warm int
	// Max bounds the actors the pool creates for a burst.
	Max int
	// IdleAfter is how long a running actor goes without a lease before the
	// pool suspends it.
	IdleAfter time.Duration
	// Interval is how often Run reconciles when the queue has not changed,
	// to see what only Substrate knows: crashes, finished resumes, a worker
	// with room for a resume that failed, and actors gone idle. Scale-up
	// waits on some of those, so keep it short.
	Interval time.Duration
	// MinInterval is the least time between two reconciles that queue
	// changes start, so a busy build costs a few reconciles a second.
	MinInterval time.Duration
	// Now returns the current time. Tests set it.
	Now func() time.Time
	// Burst, when set, is a WorkerPool the pool sizes for its actors.
	Burst *Burst
}

// Burst is a WorkerPool that only the pool sizes and only the pool's actors
// use: the pool empties it when none of them is there.
type Burst struct {
	Workers Workers
	// Name is Workers' namespace/name, the way Actor.WorkerPool names it.
	Name string
	// BaseSlots is how many of the pool's actors fit on workers that the
	// pool does not size, such as a WorkerPool on an always-on node.
	BaseSlots int
	// ActorsPerWorker is how many actors fit on one of Workers' workers.
	ActorsPerWorker int
	// MaxWorkers bounds Workers' replicas.
	MaxWorkers int
}

// Pool reconciles a tenant's actors against its queue.
type Pool struct {
	cfg Config
	// lastBusy is when each actor last held a lease, or was resumed. An
	// actor is idle when that is more than IdleAfter ago.
	lastBusy map[string]time.Time
	// unprimed holds the actors created without a successful first resume.
	// They have no snapshot yet, so the queue alone would not wake them.
	unprimed map[string]bool
	metrics  metrics

	// mu guards what the last reconcile saw, which the gauges report.
	mu       sync.Mutex
	byState  map[State]int
	queued   int
	busyBots int
	workers  int
}

// New returns a Pool. It fails on a configuration that cannot size anything.
func New(cfg Config) (*Pool, error) {
	if cfg.Actors == nil || cfg.Queue == nil || cfg.Prefix == "" {
		return nil, errors.New("actorpool: Actors, Queue, and Prefix are required")
	}
	if cfg.Warm < 0 || cfg.Max < 1 || cfg.Warm > cfg.Max {
		return nil, fmt.Errorf("actorpool: need 0 <= Warm (%d) <= Max (%d) and Max >= 1", cfg.Warm, cfg.Max)
	}
	if b := cfg.Burst; b != nil && (b.Workers == nil || b.Name == "" || b.BaseSlots < 0 || b.ActorsPerWorker < 1 || b.MaxWorkers < 1) {
		return nil, fmt.Errorf("actorpool: Burst needs Workers, Name, BaseSlots (%d) >= 0, ActorsPerWorker (%d) >= 1, and MaxWorkers (%d) >= 1",
			b.BaseSlots, b.ActorsPerWorker, b.MaxWorkers)
	}
	if cfg.IdleAfter <= 0 {
		cfg.IdleAfter = time.Minute
	}
	if cfg.Interval <= 0 {
		cfg.Interval = 5 * time.Second
	}
	if cfg.MinInterval <= 0 {
		cfg.MinInterval = 250 * time.Millisecond
	}
	if cfg.Now == nil {
		cfg.Now = time.Now
	}
	p := &Pool{cfg: cfg, lastBusy: map[string]time.Time{}, unprimed: map[string]bool{}}
	p.metrics = newMetrics(p)
	return p, nil
}

// Run reconciles when the queue changes, and every Interval, until ctx ends.
// A failed reconcile is logged and tried again next time.
func (p *Pool) Run(ctx context.Context) error {
	changed := make(chan struct{}, 1)
	go p.watch(ctx, changed)
	tick := time.NewTicker(p.cfg.Interval)
	defer tick.Stop()
	for {
		last := time.Now()
		if err := p.Reconcile(ctx); err != nil {
			slog.WarnContext(ctx, "reconcile failed", "err", err)
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-tick.C:
		case <-changed:
			timer := time.NewTimer(time.Until(last.Add(p.cfg.MinInterval)))
			select {
			case <-ctx.Done():
				timer.Stop()
				return ctx.Err()
			case <-timer.C:
			}
		}
	}
}

// watch signals changed, without blocking, each time the queue changes. It
// opens a broken watch again after Interval; Run's ticker covers the gap.
func (p *Pool) watch(ctx context.Context, changed chan<- struct{}) {
	signal := func() {
		select {
		case changed <- struct{}{}:
		default:
		}
	}
	for {
		err := p.cfg.Queue.Watch(ctx, signal)
		if ctx.Err() != nil {
			return
		}
		slog.WarnContext(ctx, "queue watch stopped", "err", err)
		timer := time.NewTimer(p.cfg.Interval)
		select {
		case <-ctx.Done():
			timer.Stop()
			return
		case <-timer.C:
		}
	}
}

// Reconcile brings the pool's actors in line with the queue once. It makes
// at most one change to each actor and returns the first error.
func (p *Pool) Reconcile(ctx context.Context) (err error) {
	ctx, span := telemetry.Tracer().Start(ctx, "pool.reconcile")
	start := time.Now()
	defer func() {
		p.metrics.reconcile.Record(ctx, time.Since(start).Seconds(), metric.WithAttributes(telemetry.AttrOutcome.String(outcome(err))))
		if err != nil {
			span.RecordError(err)
			span.SetStatus(codes.Error, err.Error())
		}
		span.End()
	}()
	all, err := p.cfg.Actors.List(ctx)
	if err != nil {
		return fmt.Errorf("listing actors: %w", err)
	}
	queued, busyIDs, err := p.cfg.Queue.Status(ctx)
	if err != nil {
		return fmt.Errorf("reading queue: %w", err)
	}
	now := p.cfg.Now()
	busy := map[string]bool{}
	for _, id := range busyIDs {
		busy[id] = true
	}

	var owned []Actor
	for _, a := range all {
		if strings.HasPrefix(a.Name, p.cfg.Prefix) {
			owned = append(owned, a)
		}
	}
	slices.SortFunc(owned, func(a, b Actor) int { return strings.Compare(a.Name, b.Name) })

	var suspended, unprimed, idle, crashed []string
	names := map[string]bool{}
	running := 0
	byState := map[State]int{}
	for _, a := range owned {
		names[a.Name] = true
		byState[a.State]++
		if a.State != StateSuspended {
			delete(p.unprimed, a.Name)
		}
		switch a.State {
		case StateSuspended:
			if p.unprimed[a.Name] {
				unprimed = append(unprimed, a.Name)
			} else {
				suspended = append(suspended, a.Name)
			}
		case StateCrashed:
			crashed = append(crashed, a.Name)
		case StateRunning, StateResuming:
			running++
			if busy[a.Name] || a.State == StateResuming {
				p.lastBusy[a.Name] = now
			} else if last, ok := p.lastBusy[a.Name]; !ok {
				// First sight of a running actor: give it IdleAfter to
				// lease before calling it idle.
				p.lastBusy[a.Name] = now
			} else if now.Sub(last) >= p.cfg.IdleAfter {
				idle = append(idle, a.Name)
			}
		}
	}
	for name := range p.lastBusy {
		if !names[name] {
			delete(p.lastBusy, name)
		}
	}
	for name := range p.unprimed {
		if !names[name] {
			delete(p.unprimed, name)
		}
	}

	// Resuming actors count as free: they lease as soon as they are up.
	free := running - len(busy)
	need := queued - free
	p.mu.Lock()
	p.byState, p.queued, p.busyBots = byState, queued, len(busy)
	p.mu.Unlock()
	span.SetAttributes(
		attribute.Int("ci_substrate.queued", queued),
		attribute.Int("ci_substrate.actors", len(owned)),
		attribute.Int("ci_substrate.actors_busy", len(busy)),
		attribute.Int("ci_substrate.need", need),
	)

	var errs []error
	for _, name := range crashed {
		slog.WarnContext(ctx, "deleting crashed actor", "actor", name)
		if err := p.do(ctx, "delete", name, p.cfg.Actors.Delete); err != nil {
			errs = append(errs, fmt.Errorf("deleting %s: %w", name, err))
		}
	}
	total := len(owned) - len(crashed)

	// A failed resume still counts against need: the usual cause is a full
	// worker pool, which more actors would not fix.
	need -= len(unprimed)
	resumes := suspended[:min(max(need, 0), len(suspended))]
	suspended = suspended[len(resumes):]
	need -= len(resumes)
	// Below Warm, create actors too: their first run leaves the snapshot
	// that makes a later resume warm.
	creates := 0
	for (need-creates > 0 || total+creates < p.cfg.Warm) && total+creates < p.cfg.Max {
		creates++
	}
	if err := p.scaleWorkers(ctx, owned, running+byState[StateSuspending], len(unprimed)+len(resumes)+creates); err != nil {
		errs = append(errs, err)
	}

	for _, name := range unprimed {
		slog.InfoContext(ctx, "resuming new actor again", "actor", name)
		if err := p.do(ctx, "resume", name, p.cfg.Actors.Resume); err != nil {
			errs = append(errs, fmt.Errorf("resuming new %s: %w", name, err))
			continue
		}
		delete(p.unprimed, name)
		p.lastBusy[name] = now
	}
	for _, name := range resumes {
		slog.InfoContext(ctx, "resuming actor for queued work", "actor", name, "queued", queued)
		if err := p.do(ctx, "resume", name, p.cfg.Actors.Resume); err != nil {
			errs = append(errs, fmt.Errorf("resuming %s: %w", name, err))
			continue
		}
		p.lastBusy[name] = now
	}
	for range creates {
		name := p.freeName(names)
		names[name] = true
		total++
		slog.InfoContext(ctx, "creating actor", "actor", name, "queued", queued, "total", total)
		if err := p.do(ctx, "create", name, p.cfg.Actors.Create); err != nil {
			errs = append(errs, fmt.Errorf("creating %s: %w", name, err))
			continue
		}
		if err := p.do(ctx, "resume", name, p.cfg.Actors.Resume); err != nil {
			p.unprimed[name] = true
			errs = append(errs, fmt.Errorf("resuming new %s: %w", name, err))
			continue
		}
		p.lastBusy[name] = now
	}

	// Keep as many idle runners as there are queued jobs still waiting for
	// one.
	keep := max(0, queued-(free-len(idle)))
	for _, name := range idle {
		if keep > 0 {
			keep--
			continue
		}
		slog.InfoContext(ctx, "suspending idle actor", "actor", name, "idle", now.Sub(p.lastBusy[name]).Round(time.Second))
		if err := p.do(ctx, "suspend", name, p.cfg.Actors.Suspend); err != nil {
			errs = append(errs, fmt.Errorf("suspending %s: %w", name, err))
		}
	}

	for total > p.cfg.Warm && len(suspended) > 0 {
		name := suspended[len(suspended)-1]
		suspended = suspended[:len(suspended)-1]
		slog.InfoContext(ctx, "deleting surplus actor", "actor", name, "total", total, "warm", p.cfg.Warm)
		if err := p.do(ctx, "delete", name, p.cfg.Actors.Delete); err != nil {
			errs = append(errs, fmt.Errorf("deleting %s: %w", name, err))
			continue
		}
		total--
	}
	return errors.Join(errs...)
}

// scaleWorkers sizes the burst WorkerPool for awake actors plus waking ones,
// which this reconcile resumes or creates next. It grows the pool first so
// those resumes find room. It shrinks the pool only when nothing is waking
// and none of the pool's actors is on it, because Kubernetes picks which
// worker to stop and Substrate crashes the actor on it.
func (p *Pool) scaleWorkers(ctx context.Context, owned []Actor, awake, waking int) error {
	b := p.cfg.Burst
	if b == nil {
		return nil
	}
	have, err := b.Workers.Replicas(ctx)
	if err != nil {
		return fmt.Errorf("reading %s replicas: %w", b.Name, err)
	}
	p.setWorkers(have)
	want := min(b.MaxWorkers, ceilDiv(max(0, awake+waking-b.BaseSlots), b.ActorsPerWorker))
	occupied := slices.ContainsFunc(owned, func(a Actor) bool { return a.WorkerPool == b.Name })
	if want == have || (want < have && (waking > 0 || occupied)) {
		return nil
	}
	slog.InfoContext(ctx, "scaling workers", "workerpool", b.Name, "from", have, "to", want, "awake", awake, "waking", waking)
	err = p.observe(ctx, "scale", attribute.String("ci_substrate.workerpool", b.Name), func(ctx context.Context) error {
		return b.Workers.Scale(ctx, want)
	})
	if err != nil {
		return fmt.Errorf("scaling %s to %d: %w", b.Name, want, err)
	}
	p.setWorkers(want)
	return nil
}

func (p *Pool) setWorkers(n int) {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.workers = n
}

func ceilDiv(a, b int) int {
	return (a + b - 1) / b
}

// do runs one change to an actor, with a span and metrics.
func (p *Pool) do(ctx context.Context, op, name string, f func(context.Context, string) error) error {
	return p.observe(ctx, op, attribute.String("ci_substrate.actor", name), func(ctx context.Context) error {
		return f(ctx, name)
	})
}

// observe runs one change, with a span and metrics.
func (p *Pool) observe(ctx context.Context, op string, target attribute.KeyValue, f func(context.Context) error) error {
	ctx, span := telemetry.Tracer().Start(ctx, "pool."+op, trace.WithAttributes(target))
	defer span.End()
	start := time.Now()
	err := f(ctx)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
	}
	attrs := metric.WithAttributes(attribute.String("op", op), telemetry.AttrOutcome.String(outcome(err)))
	p.metrics.operations.Add(ctx, 1, attrs)
	p.metrics.duration.Record(ctx, time.Since(start).Seconds(), attrs)
	return err
}

func outcome(err error) string {
	if err != nil {
		return "error"
	}
	return "ok"
}

// freeName returns the lowest-numbered name with the prefix not in names.
func (p *Pool) freeName(names map[string]bool) string {
	for i := 0; ; i++ {
		name := fmt.Sprintf("%s%d", p.cfg.Prefix, i)
		if !names[name] {
			return name
		}
	}
}
