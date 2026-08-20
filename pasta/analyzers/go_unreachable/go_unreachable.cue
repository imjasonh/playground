// go_unreachable is a syntactic port of
// golang.org/x/tools/go/analysis/passes/unreachable.
//
// Pasta flags the statement immediately after `return` or `panic(...)`
// in the same statement list. It does not model labels, breaks, or
// if/else reachability the way the original CFG walk does.

package go_unreachable

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

_deadStmt: {
	capture: "dead"
	pattern: {
		node: [
			"expression_statement",
			"return_statement",
			"if_statement",
			"for_statement",
			"short_var_declaration",
			"assignment_statement",
			"go_statement",
			"defer_statement",
			"var_declaration",
			"inc_statement",
			"dec_statement",
			"send_statement",
		]
	}
}

go_unreachable: schema.#Analyzer & {
	name:    "go_unreachable"
	version: "0.1.0"
	doc:     "Flag the statement immediately after return or panic"
	facts: {}

	rules: {
		after_return: {
			name: "after_return"
			doc:  "statement after return is unreachable"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: gopat.StmtListContainers
				adjacent: [
					{capture: "term", pattern: {node: "return_statement"}},
					_deadStmt,
				]
			}

			diagnose: {
				message:  "unreachable code"
				severity: "warning"
			}
		}

		after_panic: {
			name: "after_panic"
			doc:  "statement after panic is unreachable"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: gopat.StmtListContainers
				adjacent: [
					{
						capture: "term"
						pattern: {
							node: "expression_statement"
							children: [{
								node: "call_expression"
								fields: function: {capture: "fn", pattern: {node: "identifier"}}
								where: [{op: "eq", args: ["@fn", "panic"]}]
							}]
						}
					},
					_deadStmt,
				]
			}

			diagnose: {
				message:  "unreachable code"
				severity: "warning"
			}
		}
	}
}
