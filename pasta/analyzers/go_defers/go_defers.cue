// go_defers is a syntactic port of
// golang.org/x/tools/go/analysis/passes/defers.
//
// Arguments of a deferred call are evaluated immediately, so
// `defer f(time.Since(start))` records the duration at defer time
// (usually zero) rather than at function exit. Pasta flags `time.Since`
// as the deferred call itself or as the first or second argument of
// that call. A `time.Since` inside `defer func() { ... }()` is
// correctly delayed and is not flagged.

package go_defers

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

_since: gopat.PackageCall & {
	where: [
		{op: "eq", args: ["@pkg", "time"]},
		{op: "eq", args: ["@fn", "Since"]},
	]
}

_diag: {
	message:  "call to time.Since is not deferred"
	severity: "warning"
}

go_defers: schema.#Analyzer & {
	name:    "go_defers"
	version: "0.1.0"
	doc:     "Flag time.Since evaluated as a deferred call argument"
	facts: {}

	rules: {
		since_call: {
			name: "since_call"
			doc:  "defer time.Since(...) evaluates at defer time"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "defer_statement"
				children: [_since]
			}

			diagnose: _diag
		}

		since_first_arg: {
			name: "since_first_arg"
			doc:  "defer f(time.Since(...))"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "defer_statement"
				children: [{
					node: "call_expression"
					fields: arguments: {
						node: "argument_list"
						children: [_since]
					}
				}]
			}

			diagnose: _diag
		}

		since_second_arg: {
			name: "since_second_arg"
			doc:  "defer f(x, time.Since(...))"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "defer_statement"
				children: [{
					node: "call_expression"
					fields: arguments: {
						node: "argument_list"
						children: [gopat.Any, _since]
					}
				}]
			}

			diagnose: _diag
		}
	}
}
