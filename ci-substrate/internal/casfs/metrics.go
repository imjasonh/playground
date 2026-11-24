package casfs

import (
	"go.opentelemetry.io/otel/metric"

	"github.com/imjasonh/playground/ci-substrate/internal/telemetry"
)

var (
	hydrations = telemetry.Handle(telemetry.Meter().Int64Counter("casfs.hydrations",
		metric.WithDescription("Files casfs fetched on first read or write, by outcome.")))
	hydratedBytes = telemetry.Handle(telemetry.Meter().Int64Counter("casfs.hydrated.bytes", metric.WithUnit("By"),
		metric.WithDescription("Bytes casfs fetched to hydrate files.")))
	hydrateDuration = telemetry.Handle(telemetry.Meter().Float64Histogram("casfs.hydrate.duration", metric.WithUnit("s"),
		metric.WithDescription("Time to fetch and verify one file's bytes, which the reading action waits for."),
		metric.WithExplicitBucketBoundaries(.0005, .001, .0025, .005, .01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10)))
	execRoots = telemetry.Handle(telemetry.Meter().Int64UpDownCounter("casfs.exec_roots",
		metric.WithDescription("Exec roots materialized on inputs volumes and not yet dropped.")))
	treeLoadDuration = telemetry.Handle(telemetry.Meter().Float64Histogram("casfs.tree_load.duration", metric.WithUnit("s"),
		metric.WithDescription("Time to load an input root's Directory tree for an exec root on a volume, by outcome."),
		metric.WithExplicitBucketBoundaries(.001, .0025, .005, .01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10)))
)
