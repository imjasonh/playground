// go_stringintconv is a syntactic port of
// golang.org/x/tools/go/analysis/passes/stringintconv.
//
// `string(123)` yields a single-rune string, not decimal digits.
// Without types Pasta can only flag integer literals (not `string(x)`
// where x might be []byte or rune). The fix wraps the literal in
// `rune(...)` so the conversion is explicit.

package go_stringintconv

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_stringintconv: schema.#Analyzer & {
	name:    "go_stringintconv"
	version: "0.1.0"
	doc:     "Flag string(int-literal), which yields a one-rune string"

	facts: {}

	rules: int_literal: {
		name: "int_literal"
		doc:  "string(123) is a rune, not decimal digits"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {
					capture: "args"
					pattern: {
						node: "argument_list"
						children: [{capture: "arg", pattern: {node: "int_literal"}}]
					}
				}
			}
			where: [
				{op: "eq", args: ["@fn", "string"]},
				{op: "named_child_count", args: ["@args", "1"]},
			]
		}

		diagnose: {
			message:  "conversion from integer to string yields a string of one rune, not a string of digits"
			severity: "warning"
		}

		rewrite: edits: [{
			position: "before"
			anchor:   "arg"
			text:     "rune("
		}, {
			position: "after"
			anchor:   "arg"
			text:     ")"
		}]
	}
}
