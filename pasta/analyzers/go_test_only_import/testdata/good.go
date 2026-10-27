package good

import (
	"context"

	"go.opentelemetry.io/otel/trace"

	// A subpackage path is a different string than the exact import this
	// rule matches, so it's not flagged here either; nothing stops someone
	// importing a testtrace subpackage outside a test, but nothing in this
	// repo has a reason to.
	_ "github.com/imjasonh/playground/testtrace/examples/gcp"
)

func f(ctx context.Context, span trace.Span) {
	_ = span
}
