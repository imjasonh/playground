package kube

import (
	"context"

	"github.com/chainguard-dev/clog"
)

// logAttr marks a context that already carries one set of log attributes,
// so a later withLog for the same name does not repeat the keys.
type logAttr struct{ name string }

// withLog returns ctx with attrs on its logger. The same name on a child
// of that context leaves the logger unchanged.
func withLog(ctx context.Context, name string, attrs ...any) context.Context {
	if ctx.Value(logAttr{name}) != nil {
		return ctx
	}
	ctx = clog.WithLogger(ctx, clog.FromContext(ctx).With(attrs...))
	return context.WithValue(ctx, logAttr{name}, true)
}
