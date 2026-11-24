package exec

import (
	"context"

	repb "github.com/bazelbuild/remote-apis/build/bazel/remote/execution/v2"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"

	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
)

// durationBuckets spans a cached compile to a long test, in seconds.
var durationBuckets = metric.WithExplicitBucketBoundaries(.005, .01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10, 30, 60, 120, 300, 600, 1800)

type metrics struct {
	executions  metric.Int64Counter
	completed   metric.Int64Counter
	queueTime   metric.Float64Histogram
	runTime     metric.Float64Histogram
	expirations metric.Int64Counter
}

// newMetrics makes the scheduler's instruments, and gauges that read s's
// queue each time the metrics are collected.
func newMetrics(s *Scheduler) metrics {
	m := telemetry.Meter()
	ms := metrics{
		executions: telemetry.Handle(m.Int64Counter("scheduler.executions",
			metric.WithDescription("Execute calls, by result: cached (served from the action cache), merged (joined an identical in-flight action), or queued."))),
		completed: telemetry.Handle(m.Int64Counter("scheduler.jobs.completed",
			metric.WithDescription("Jobs that finished, by outcome: ok, exit_nonzero, error (the runner failed), or lease_expired."))),
		queueTime: telemetry.Handle(m.Float64Histogram("scheduler.queue.duration", metric.WithUnit("s"),
			metric.WithDescription("Time a job waited for a runner, per attempt."), durationBuckets)),
		runTime: telemetry.Handle(m.Float64Histogram("scheduler.execution.duration", metric.WithUnit("s"),
			metric.WithDescription("Time from a runner's lease to its Complete, including input and output transfer."), durationBuckets)),
		expirations: telemetry.Handle(m.Int64Counter("scheduler.lease.expirations",
			metric.WithDescription("Leases that ran out because a runner stopped heartbeating."))),
	}
	jobs := telemetry.Handle(m.Int64ObservableGauge("scheduler.jobs",
		metric.WithDescription("Jobs in the scheduler, by stage: queued or executing.")))
	waiting := telemetry.Handle(m.Int64ObservableGauge("scheduler.runners.waiting",
		metric.WithDescription("Runners blocked in Lease waiting for a job.")))
	busy := telemetry.Handle(m.Int64ObservableGauge("scheduler.runners.busy",
		metric.WithDescription("Runners holding a lease.")))
	telemetry.Handle(m.RegisterCallback(func(_ context.Context, o metric.Observer) error {
		type key struct {
			instance string
			stage    string
		}
		counts := map[key]int64{}
		bots := map[string]map[string]bool{}
		s.mu.Lock()
		for _, j := range s.jobs {
			switch j.stage {
			case repb.ExecutionStage_QUEUED:
				counts[key{j.instance, "queued"}]++
			case repb.ExecutionStage_EXECUTING:
				counts[key{j.instance, "executing"}]++
				if j.botID != "" {
					if bots[j.instance] == nil {
						bots[j.instance] = map[string]bool{}
					}
					bots[j.instance][j.botID] = true
				}
			}
		}
		nwaiting := int64(len(s.waiters))
		s.mu.Unlock()
		for k, n := range counts {
			o.ObserveInt64(jobs, n, metric.WithAttributes(telemetry.AttrInstance.String(k.instance), attribute.String("stage", k.stage)))
		}
		for instance, b := range bots {
			o.ObserveInt64(busy, int64(len(b)), metric.WithAttributes(telemetry.AttrInstance.String(instance)))
		}
		o.ObserveInt64(waiting, nwaiting)
		return nil
	}, jobs, waiting, busy))
	return ms
}
