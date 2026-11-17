package actorpool

import (
	"context"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"

	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
)

type metrics struct {
	operations metric.Int64Counter
	duration   metric.Float64Histogram
	reconcile  metric.Float64Histogram
}

// newMetrics makes the pool's instruments, and gauges that report what p's
// last reconcile saw.
func newMetrics(p *Pool) metrics {
	m := telemetry.Meter()
	ms := metrics{
		operations: telemetry.Handle(m.Int64Counter("pool.operations",
			metric.WithDescription("Changes the pool made to actors, by op (create, resume, suspend, delete) and outcome."))),
		duration: telemetry.Handle(m.Float64Histogram("pool.operation.duration", metric.WithUnit("s"),
			metric.WithDescription("Time Substrate took to accept one change to an actor, by op."),
			metric.WithExplicitBucketBoundaries(.01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10, 30, 60))),
		reconcile: telemetry.Handle(m.Float64Histogram("pool.reconcile.duration", metric.WithUnit("s"),
			metric.WithDescription("Time one reconcile took, by outcome."),
			metric.WithExplicitBucketBoundaries(.01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10, 30, 60))),
	}
	actors := telemetry.Handle(m.Int64ObservableGauge("pool.actors",
		metric.WithDescription("Actors the pool owns, by state.")))
	queued := telemetry.Handle(m.Int64ObservableGauge("pool.queued",
		metric.WithDescription("Jobs waiting for a runner in the tenant's queue.")))
	busy := telemetry.Handle(m.Int64ObservableGauge("pool.actors.busy",
		metric.WithDescription("Actors whose runner holds a lease.")))
	telemetry.Handle(m.RegisterCallback(func(_ context.Context, o metric.Observer) error {
		p.mu.Lock()
		defer p.mu.Unlock()
		for _, st := range []State{StateUnknown, StateSuspended, StateResuming, StateRunning, StateSuspending, StateCrashed} {
			o.ObserveInt64(actors, int64(p.byState[st]), metric.WithAttributes(attribute.String("state", st.String())))
		}
		o.ObserveInt64(queued, int64(p.queued))
		o.ObserveInt64(busy, int64(p.busyBots))
		return nil
	}, actors, queued, busy))
	return ms
}
