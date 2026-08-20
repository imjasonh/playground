// go_appends is a syntactic port of
// golang.org/x/tools/go/analysis/passes/appends.
//
// `append(s)` with only the destination slice and no values is almost
// always a mistake — the call is a no-op and the author meant to pass
// elements or another slice. Pasta cannot prove the callee is the
// builtin (no types), so this flags identifier `append` with a single
// argument.

package go_appends

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_appends: schema.#Analyzer & {
	name:    "go_appends"
	version: "0.1.0"
	doc:     "Flag append(s) with no values to append"

	facts: {}

	rules: no_values: {
		name: "no_values"
		doc:  "append with only the destination slice is a no-op"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {capture: "args"}
			}
			where: [
				{op: "eq", args: ["@fn", "append"]},
				{op: "named_child_count", args: ["@args", "1"]},
			]
		}

		diagnose: {
			message:  "append with no values"
			severity: "warning"
		}
	}
}
