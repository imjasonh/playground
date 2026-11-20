// go_time_after_select flags `case <-time.After(...)` inside a select
// statement that is contained within a for loop.
// time.After creates an active timer on each iteration that cannot be
// garbage-collected until it expires, causing a memory leak.
// Prefer time.NewTimer and timer.Reset instead.

package go_time_after_select

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_time_after_select: schema.#Analyzer & {
	name:    "go_time_after_select"
	version: "0.1.0"
	doc:     "Flag time.After in a for-select loop (leaks memory until timer expires)"
	facts: {}

	rules: for_select: {
		name:      "for_select"
		doc:       "time.After in a communication case inside a for loop leaks memory"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "selector_expression"
					fields: {
						operand: {capture: "pkg", pattern: {node: "identifier"}}
						field:   {capture: "fn", pattern: {node: "field_identifier"}}
					}
				}
			}
			where: [
				{op: "eq", args: ["@pkg", "time"]},
				{op: "eq", args: ["@fn", "After"]},
				{op: "ancestor_is", args: ["@_root", "communication_case"]},
				{op: "ancestor_is", args: ["@_root", "for_statement"]},
			]
		}

		diagnose: {
			message:  "time.After in a for-select loop will leak memory until timer expires; use time.NewTimer and Reset instead"
			severity: "hint"
		}
	}
}
