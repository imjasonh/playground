// go_lostcancel is a syntactic port of
// golang.org/x/tools/go/analysis/passes/lostcancel.
//
// Pasta flags discarding the cancel function from context.WithCancel
// and friends by assigning it to `_`. The original analyzer also
// walks the CFG for unused named cancel variables; that needs
// control-flow facts Pasta does not have.

package go_lostcancel

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

_withCall: gopat.PackageCall & {
	where: [
		{op: "eq", args: ["@pkg", "context"]},
		{op: "matches", args: ["@fn", "^With(Cancel|CancelCause|Deadline|DeadlineCause|Timeout|TimeoutCause)$"]},
	]
}

_discard: {
	languages: [golang.Name]
	requires: []
	provides: []

	diagnose: {
		message:  "the cancel function returned by context.@fn should be called, not discarded"
		severity: "warning"
	}
}

go_lostcancel: schema.#Analyzer & {
	name:    "go_lostcancel"
	version: "0.1.0"
	doc:     "Flag discarding the cancel function from context.WithCancel and similar"
	facts: {}

	rules: {
		short_discard: _discard & {
			name: "short_discard"
			doc:  "ctx, _ := context.WithCancel(...) discards cancel"
			match: {
				node: "short_var_declaration"
				fields: {
					left: {
						node: "expression_list"
						children: [
							{},
							{capture: "cancel", pattern: gopat.Identifier},
						]
					}
					right: {
						node: "expression_list"
						children: [{pattern: _withCall}]
					}
				}
				where: [{op: "eq", args: ["@cancel", "_"]}]
			}
		}

		assign_discard: _discard & {
			name: "assign_discard"
			doc:  "_, _ = context.WithCancel(...) discards cancel"
			match: {
				node: "assignment_statement"
				fields: {
					left: {
						node: "expression_list"
						children: [
							{},
							{capture: "cancel", pattern: gopat.Identifier},
						]
					}
					right: {
						node: "expression_list"
						children: [{pattern: _withCall}]
					}
				}
				where: [{op: "eq", args: ["@cancel", "_"]}]
			}
		}
	}
}
