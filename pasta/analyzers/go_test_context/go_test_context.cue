// go_test_context requires t.Context() in tests.
//
// The Google Go decisions guide allows context.Background in main,
// init, and tests. This repo allows it in main and init. A test uses
// t.Context() (benchmarks use b.Context(), fuzz targets use
// f.Context()), which cancels when the test finishes.
// https://google.github.io/styleguide/go/decisions#contexts
//
// Scope is filename-based (`*_test.go`). Pasta has no ancestor-name
// predicate, so the check covers the whole file. Helpers in test
// files that lack a *testing.T may need pasta:ignore. Rewrites assume
// the conventional `t` parameter name.

package go_test_context

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_test_context: schema.#Analyzer & {
	name:    "go_test_context"
	version: "0.1.0"
	doc:     "Prefer t.Context() over context.Background/TODO in tests"
	facts: {}

	rules: use_t_context: {
		name: "use_t_context"
		doc:  "context.Background/TODO in tests should be t.Context()"
		languages: [golang.Name]
		requires: []
		provides: []
		file_match: ["*_test.go"]

		match: gopat.PackageCall & {
			fields: arguments: {
				capture: "args"
				pattern: {node: "argument_list"}
			}
			where: [
				{op: "eq", args: ["@pkg", "context"]},
				{op: "matches", args: ["@fn", "^(Background|TODO)$"]},
				{op: "named_child_count", args: ["@args", "0"]},
			]
		}

		diagnose: {
			message:  "use t.Context() instead of context.@fn() in tests"
			severity: "warning"
		}

		rewrite: edits: [{
			target:      "_root"
			replacement: "t.Context()"
		}]
	}
}
