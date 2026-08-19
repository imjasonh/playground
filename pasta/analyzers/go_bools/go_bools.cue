// go_bools is a syntactic port of
// golang.org/x/tools/go/analysis/passes/bools.
//
// It flags two classes of boolean-operator mistakes that are visible
// from the tree without types:
//
//   - redundant: `x || x` and `x && x`
//   - suspect: `x != a || x != b` (always true when a != b) and
//     `x == a && x == b` (always false when a != b)
//
// Nested commutative sets and side-effect filtering from the original
// analyzer are out of reach for tree-sitter matching.

package go_bools

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

_redundant: {
	_op:   "||" | "&&"
	_name: "or" | "and"

	out: {
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "binary_expression"
			fields: {
				left:     {capture: "left", pattern: gopat.Identifier}
				operator: {capture: "op"}
				right:    {capture: "right", pattern: gopat.Identifier}
			}
			where: [
				{op: "token_eq", args: ["@op", _op]},
				{op: "same_ident", args: ["@left", "@right"]},
			]
		}

		diagnose: {
			message:  "redundant \(_name)"
			severity: "warning"
		}
	}
}

_suspect: {
	_outer: "||" | "&&"
	_inner: "!=" | "=="
	_name:  "or" | "and"

	out: {
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "binary_expression"
			fields: {
				operator: {capture: "outer"}
				left: {
					pattern: {
						node: "binary_expression"
						fields: {
							operator: {capture: "lop"}
							left:     {capture: "x1", pattern: gopat.Identifier}
							right:    {capture: "c1"}
						}
						where: [{op: "token_eq", args: ["@lop", _inner]}]
					}
				}
				right: {
					pattern: {
						node: "binary_expression"
						fields: {
							operator: {capture: "rop"}
							left:     {capture: "x2", pattern: gopat.Identifier}
							right:    {capture: "c2"}
						}
						where: [{op: "token_eq", args: ["@rop", _inner]}]
					}
				}
			}
			where: [
				{op: "token_eq", args: ["@outer", _outer]},
				{op: "same_ident", args: ["@x1", "@x2"]},
				{op: "neq", args: ["@c1", "@c2"]},
			]
		}

		diagnose: {
			message:  "suspect \(_name)"
			severity: "warning"
		}
	}
}

go_bools: schema.#Analyzer & {
	name:    "go_bools"
	version: "0.1.0"
	doc:     "Flag redundant and suspect boolean operator combinations"
	facts: {}

	rules: {
		redundant_or: (_redundant & {_op: "||", _name: "or"}).out & {
			name: "redundant_or"
			doc:  "x || x is redundant"
		}
		redundant_and: (_redundant & {_op: "&&", _name: "and"}).out & {
			name: "redundant_and"
			doc:  "x && x is redundant"
		}
		suspect_or: (_suspect & {_outer: "||", _inner: "!=", _name: "or"}).out & {
			name: "suspect_or"
			doc:  "x != a || x != b is always true when a and b differ"
		}
		suspect_and: (_suspect & {_outer: "&&", _inner: "==", _name: "and"}).out & {
			name: "suspect_and"
			doc:  "x == a && x == b is always false when a and b differ"
		}
	}
}
