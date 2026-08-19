// go_copylock is a syntactic port of
// golang.org/x/tools/go/analysis/passes/copylock.
//
// Passing `sync.Mutex` or `sync.RWMutex` by value copies the lock.
// Pasta flags those types as function or method parameters when they
// are not pointers. It does not walk nested structs the way the
// original analyzer does.

package go_copylock

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_copylock: schema.#Analyzer & {
	name:    "go_copylock"
	version: "0.1.0"
	doc:     "Flag sync.Mutex / sync.RWMutex passed by value as a parameter"

	facts: {}

	rules: param_by_value: {
		name: "param_by_value"
		doc:  "func parameter of type sync.Mutex copies the lock"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "parameter_declaration"
			fields: type: {
				capture: "typ"
				pattern: {
					node: "qualified_type"
					fields: {
						package: {capture: "pkg"}
						name:    {capture: "name"}
					}
				}
			}
			where: [
				{op: "eq", args: ["@pkg", "sync"]},
				{op: "matches", args: ["@name", "^(Mutex|RWMutex)$"]},
			]
		}

		diagnose: {
			message:  "passes lock by value: sync.@name"
			severity: "warning"
		}
	}
}
