package bot

import (
	"os"
	"runtime"
	"syscall"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

// rusageAttributes extracts POSIX resource usage from a completed process state
// as OpenTelemetry span attributes.
func rusageAttributes(ps *os.ProcessState) []attribute.KeyValue {
	if ps == nil {
		return nil
	}
	ru, ok := ps.SysUsage().(*syscall.Rusage)
	if !ok || ru == nil {
		return nil
	}
	userSec := (time.Duration(ru.Utime.Sec)*time.Second + time.Duration(ru.Utime.Usec)*time.Microsecond).Seconds()
	sysSec := (time.Duration(ru.Stime.Sec)*time.Second + time.Duration(ru.Stime.Usec)*time.Microsecond).Seconds()
	maxRSSBytes := int64(ru.Maxrss)
	if runtime.GOOS == "linux" {
		// Linux reports ru_maxrss in kibibytes; Darwin reports bytes.
		maxRSSBytes *= 1024
	}
	return []attribute.KeyValue{
		attribute.Float64("ci_substrate.rusage.user_seconds", userSec),
		attribute.Float64("ci_substrate.rusage.system_seconds", sysSec),
		attribute.Int64("ci_substrate.rusage.max_rss_bytes", maxRSSBytes),
		attribute.Int64("ci_substrate.rusage.inblock", int64(ru.Inblock)),
		attribute.Int64("ci_substrate.rusage.oublock", int64(ru.Oublock)),
	}
}
