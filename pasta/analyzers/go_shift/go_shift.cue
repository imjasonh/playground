// go_shift is a syntactic port of
// golang.org/x/tools/go/analysis/passes/shift.
//
// A shift count of 64 or more is always too large for Go's integer
// types. Without types Pasta can only flag integer-literal counts;
// variables and computed counts are left to the original analyzer.

package go_shift

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

_shiftOp: {
	_tok: "<<" | ">>"

	out: {
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "binary_expression"
			fields: {
				operator: {capture: "op"}
				right:    {capture: "n", pattern: {node: "int_literal"}}
			}
			where: [
				{op: "token_eq", args: ["@op", _tok]},
				{op: "matches", args: ["@n", "^(6[4-9]|[7-9][0-9]|[1-9][0-9]{2,})$"]},
			]
		}

		diagnose: {
			message:  "shift count @n is too large for a 64-bit integer"
			severity: "warning"
		}
	}
}

go_shift: schema.#Analyzer & {
	name:    "go_shift"
	version: "0.1.0"
	doc:     "Flag shifts by a constant of 64 or more"
	facts: {}

	rules: {
		shl: (_shiftOp & {_tok: "<<"}).out & {
			name: "shl"
			doc:  "x << 64 and larger"
		}
		shr: (_shiftOp & {_tok: ">>"}).out & {
			name: "shr"
			doc:  "x >> 64 and larger"
		}
	}
}
