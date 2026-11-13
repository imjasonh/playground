package telemetry

import (
	"context"
	"syscall"

	"go.opentelemetry.io/otel/metric"
)

// ObserveDisk reports the used and total bytes of the filesystem holding
// dir as disk.usage and disk.capacity, labeled with dir, so a full blob
// store shows up before writes start failing.
func ObserveDisk(dir string) {
	m := Meter()
	used := Handle(m.Int64ObservableUpDownCounter("disk.usage",
		metric.WithUnit("By"), metric.WithDescription("Bytes used on the filesystem holding the directory.")))
	total := Handle(m.Int64ObservableUpDownCounter("disk.capacity",
		metric.WithUnit("By"), metric.WithDescription("Size of the filesystem holding the directory.")))
	attrs := metric.WithAttributes(attrDir.String(dir))
	Handle(m.RegisterCallback(func(_ context.Context, o metric.Observer) error {
		var st syscall.Statfs_t
		if err := syscall.Statfs(dir, &st); err != nil {
			return err
		}
		bs := int64(st.Bsize)
		o.ObserveInt64(total, int64(st.Blocks)*bs, attrs)
		o.ObserveInt64(used, int64(st.Blocks-st.Bfree)*bs, attrs)
		return nil
	}, used, total))
}
