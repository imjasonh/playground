// go_sprintf_no_verbs flags `fmt.Sprintf(...)` calls where the only
// argument is a string literal containing no `%` format verbs.
// The call allocates and parses format verbs needlessly.

package go_sprintf_no_verbs

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_sprintf_no_verbs: schema.#Analyzer & {
	name:    "go_sprintf_no_verbs"
	version: "0.1.0"
	doc:     "Flag fmt.Sprintf called with a literal format string containing no format verbs"
	facts: {}

	rules: no_verbs: {
		name:      "no_verbs"
		doc:       "fmt.Sprintf with a single string literal containing no % verbs is redundant"
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
				arguments: {
					capture: "args"
					pattern: {
						node: "argument_list"
						children: [{
							capture: "lit"
							pattern: {
								node: ["interpreted_string_literal", "raw_string_literal"]
							}
						}]
					}
				}
			}
			where: [
				{op: "eq", args: ["@pkg", "fmt"]},
				{op: "eq", args: ["@fn", "Sprintf"]},
				{op: "named_child_count", args: ["@args", "1"]},
				{op: "not_matches", args: ["@lit", "%"]},
			]
		}

		diagnose: {
			message:  "fmt.Sprintf with a constant string and no verbs is redundant; use the string literal directly"
			severity: "warning"
		}

		rewrite: edits: [{target: "_root", replacement: "@lit"}]
	}
}
