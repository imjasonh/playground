// go_testinggoroutine is a syntactic port of
// golang.org/x/tools/go/analysis/passes/testinggoroutine.
//
// `t.Fatal` and similar methods must run in the test goroutine. Pasta
// flags those calls when they sit under a `go` statement. It does not
// follow named helpers started with `go helper()`.

package go_testinggoroutine

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_testinggoroutine: schema.#Analyzer & {
	name:    "go_testinggoroutine"
	version: "0.1.0"
	doc:     "Flag t.Fatal and similar calls from a goroutine started by the test"

	facts: {}

	rules: fatal_in_go: {
		name: "fatal_in_go"
		doc:  "t.Fatal / FailNow / SkipNow from a non-test goroutine"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: function: {
				node: "selector_expression"
				fields: field: {capture: "meth", pattern: gopat.FieldIdentifier}
			}
			where: [
				{op: "matches", args: ["@meth", "^(Fatal|Fatalf|FailNow|Skip|Skipf|SkipNow)$"]},
				{op: "ancestor_is", args: ["@_root", "go_statement"]},
			]
		}

		diagnose: {
			message:  "call to @meth from a non-test goroutine"
			severity: "warning"
		}
	}
}
