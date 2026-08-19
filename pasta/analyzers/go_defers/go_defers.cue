// go_defers is a syntactic port of
// golang.org/x/tools/go/analysis/passes/defers.
//
// Arguments of a deferred call are evaluated immediately, so
// `defer f(time.Since(start))` records the duration at defer time
// (usually zero) rather than at function exit. Pasta flags a
// `time.Since` call nested under `defer`.

package go_defers

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_defers: schema.#Analyzer & {
	name:    "go_defers"
	version: "0.1.0"
	doc:     "Flag time.Since evaluated as a deferred call argument"

	facts: {}

	rules: since_arg: {
		name: "since_arg"
		doc:  "time.Since in a defer argument runs at defer time, not at exit"
		languages: [golang.Name]
		requires: []
		provides: []

		match: gopat.PackageCall & {
			where: [
				{op: "eq", args: ["@pkg", "time"]},
				{op: "eq", args: ["@fn", "Since"]},
				{op: "ancestor_is", args: ["@_root", "defer_statement"]},
			]
		}

		diagnose: {
			message:  "call to time.Since is not deferred"
			severity: "warning"
		}
	}
}
