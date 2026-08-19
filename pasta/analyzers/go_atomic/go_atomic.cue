// go_atomic is a syntactic port of
// golang.org/x/tools/go/analysis/passes/atomic.
//
// `x = atomic.AddInt32(&x, 1)` writes the *new* value back through a
// non-atomic store, racing with the atomic add. The add already
// updates `x`; the assignment is the bug. Pasta matches identifier
// `atomic.Add*` whose first argument is `&` of the same LHS name.

package go_atomic

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_atomic: schema.#Analyzer & {
	name:    "go_atomic"
	version: "0.1.0"
	doc:     "Flag assigning atomic.Add* back to the same variable"

	facts: {}

	rules: add_assign: {
		name: "add_assign"
		doc:  "x = atomic.Add*(&x, delta) is a non-atomic store of the result"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "assignment_statement"
			fields: {
				left: {
					capture: "lhs_list"
					pattern: {
						node: "expression_list"
						children: [{capture: "lhs", pattern: gopat.Identifier}]
					}
				}
				operator: {capture: "op"}
				right: {
					node: "expression_list"
					children: [
						gopat.PackageCall & {
							fields: arguments: {
								node: "argument_list"
								children: [
									{
										capture: "addr"
										pattern: {
											node: "unary_expression"
											fields: {
												operator: {capture: "amp"}
												operand:  {capture: "inner", pattern: gopat.Identifier}
											}
											where: [{op: "token_eq", args: ["@amp", "&"]}]
										}
									},
									gopat.Any,
								]
							}
						},
					]
				}
			}
			where: [
				{op: "token_eq", args: ["@op", "="]},
				{op: "eq", args: ["@pkg", "atomic"]},
				{op: "matches", args: ["@fn", "^Add(Int32|Int64|Uint32|Uint64|Uintptr)$"]},
				{op: "same_ident", args: ["@lhs", "@inner"]},
				{op: "named_child_count", args: ["@lhs_list", "1"]},
			]
		}

		diagnose: {
			message:  "direct assignment to atomic value"
			severity: "warning"
		}
	}
}
