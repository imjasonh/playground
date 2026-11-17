// Package actorpool keeps one tenant's Substrate runners sized to that
// tenant's queue. It owns the actors whose names carry its prefix, and each
// reconcile moves them along this lifecycle:
//
//   - A new actor is created and resumed once, so that its first suspend
//     leaves a memory snapshot. Resuming from that snapshot is the warm path.
//   - A queued job with no idle runner resumes a suspended actor, or creates
//     one when none is suspended and the pool is under its maximum.
//   - A running actor that has held no lease for IdleAfter is suspended.
//   - A suspended actor beyond Warm is deleted, and a crashed one is deleted
//     so the next reconcile replaces it.
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
// the bot ids holding leases.
type Queue interface {
	Status(ctx context.Context) (queued int, busy []string, err error)
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
	// Interval is how often Run reconciles.
	Interval time.Duration
	// Now returns the current time. Tests set it.
	Now func() time.Time
}

// Pool reconciles a tenant's actors against its queue.
type Pool struct {
	cfg Config
	// lastBusy is when each actor last held a lease, or was resumed. An
	// actor is idle when that is more than IdleAfter ago.
	lastBusy map[string]time.Time
	metrics  metrics

	// mu guards what the last reconcile saw, which the gauges report.
	mu       sync.Mutex
	byState  map[State]int
	queued   int
	busyBots int
}

// New returns a Pool. It fails on a configuration that cannot size anything.
func New(cfg Config) (*Pool, error) {
	if cfg.Actors == nil || cfg.Queue == nil || cfg.Prefix == "" {
		return nil, errors.New("actorpool: Actors, Queue, and Prefix are required")
	}
	if cfg.Warm < 0 || cfg.Max < 1 || cfg.Warm > cfg.Max {
		return nil, fmt.Errorf("actorpool: need 0 <= Warm (%d) <= Max (%d) and Max >= 1", cfg.Warm, cfg.Max)
	}
	if cfg.IdleAfter <= 0 {
		cfg.IdleAfter = time.Minute
	}
	if cfg.Interval <= 0 {
		cfg.Interval = 5 * time.Second
	}
	if cfg.Now == nil {
		cfg.Now = time.Now
	}
	p := &Pool{cfg: cfg, lastBusy: map[string]time.Time{}}
	p.metrics = newMetrics(p)
	return p, nil
}

// Run reconciles every Interval until ctx ends. A failed reconcile is logged
// and tried again next time.
func (p *Pool) Run(ctx context.Context) error {
	tick := time.NewTicker(p.cfg.Interval)
	defer tick.Stop()
	for {
		if err := p.Reconcile(ctx); err != nil {
			slog.WarnContext(ctx, "reconcile failed", "err", err)
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-tick.C:
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

	var suspended, idle, crashed []string
	names := map[string]bool{}
	running := 0
	byState := map[State]int{}
	for _, a := range owned {
		names[a.Name] = true
		byState[a.State]++
		switch a.State {
		case StateSuspended:
			suspended = append(suspended, a.Name)
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
	for need > 0 && len(suspended) > 0 {
		name := suspended[0]
		suspended = suspended[1:]
		need--
		slog.InfoContext(ctx, "resuming actor for queued work", "actor", name, "queued", queued)
		if err := p.do(ctx, "resume", name, p.cfg.Actors.Resume); err != nil {
			errs = append(errs, fmt.Errorf("resuming %s: %w", name, err))
			continue
		}
		p.lastBusy[name] = now
	}
	// Below Warm, create actors too: their first run leaves the snapshot
	// that makes a later resume warm.
	for (need > 0 || total < p.cfg.Warm) && total < p.cfg.Max {
		name := p.freeName(names)
		names[name] = true
		total++
		need--
		slog.InfoContext(ctx, "creating actor", "actor", name, "queued", queued, "total", total)
		if err := p.do(ctx, "create", name, p.cfg.Actors.Create); err != nil {
			errs = append(errs, fmt.Errorf("creating %s: %w", name, err))
			continue
		}
		if err := p.do(ctx, "resume", name, p.cfg.Actors.Resume); err != nil {
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

// do runs one change to an actor, with a span and metrics.
func (p *Pool) do(ctx context.Context, op, name string, f func(context.Context, string) error) error {
	ctx, span := telemetry.Tracer().Start(ctx, "pool."+op, trace.WithAttributes(attribute.String("ci_substrate.actor", name)))
	defer span.End()
	start := time.Now()
	err := f(ctx, name)
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
