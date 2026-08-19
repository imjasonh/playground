// go_waitgroup is a syntactic port of
// golang.org/x/tools/go/analysis/passes/waitgroup.
//
// `go func() { wg.Add(1); ... }()` runs Add inside the new goroutine,
// so Wait can return before Add. Pasta flags `.Add` as the first
// statement of a goroutine's function literal. It cannot prove the
// receiver is a WaitGroup.

package go_waitgroup

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_waitgroup: schema.#Analyzer & {
	name:    "go_waitgroup"
	version: "0.1.0"
	doc:     "Flag WaitGroup.Add as the first statement of a new goroutine"

	facts: {}

	rules: add_in_go: {
		name: "add_in_go"
		doc:  "wg.Add must run before go, not as the first statement inside it"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "go_statement"
			children: [{
				node: "call_expression"
				fields: function: {
					node: "func_literal"
					fields: body: {
						node: "block"
						children: [{
							node: "statement_list"
							children: [{
								node: "expression_statement"
								children: [{
									node: "call_expression"
									fields: function: {
										node: "selector_expression"
										fields: field: {capture: "meth", pattern: gopat.FieldIdentifier}
									}
									where: [{op: "eq", args: ["@meth", "Add"]}]
								}]
							}]
						}]
					}
				}
			}]
		}

		diagnose: {
			message:  "WaitGroup.Add called from inside new goroutine"
			severity: "warning"
		}
	}
}
