// rust_bool_assert_comparison flags `assert_eq!(x, true)` /
// `assert_eq!(x, false)` (and `assert_ne!` with a bool literal).
// Clippy `bool_assert_comparison` covers the same ground: write
// `assert!(x)` / `assert!(!x)` instead. Diagnose-only — rewriting
// `assert_eq!(false, x)` vs `assert_eq!(x, false)` to `assert!(!x)`
// is straightforward, but `assert_ne!` polarity is easy to get wrong
// without inspecting both sides.
//
// Not enrolled in playground `.pasta/`: Worker and CLI tests compare
// JSON bools with `assert_eq!(x, true)`.

package rust_bool_assert_comparison

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

_boolAssert: {
	_name: string
	_doc:  string
	_kids: [...]

	out: {
		name:      _name
		doc:       _doc
		languages: [rustlang.Name]
		requires: []
		provides: []

		match: {
			node: "macro_invocation"
			fields: {
				macro: {capture: "name"}
			}
			children: [
				{node: "identifier"},
				{
					node: "token_tree"
					children: _kids
				},
			]
			where: [{op: "matches", args: ["@name", "^assert_(eq|ne)$"]}]
		}

		diagnose: {
			severity: "hint"
			message:  "compare with `assert!(x)` / `assert!(!x)` instead of asserting equality to a bool literal"
		}
	}
}

rust_bool_assert_comparison: schema.#Analyzer & {
	name:    "rust_bool_assert_comparison"
	version: "0.1.0"
	doc:     "Flag assert_eq!(x, true/false) (clippy bool_assert_comparison)"
	facts: {}

	rules: {
		bool_rhs: (_boolAssert & {
			_name: "bool_rhs"
			_doc:  "assert_eq!(x, true) / assert_eq!(x, false)"
			_kids: [
				{capture: "lhs"},
				{capture: "rhs", pattern: {node: "boolean_literal"}},
			]
		}).out

		bool_lhs: (_boolAssert & {
			_name: "bool_lhs"
			_doc:  "assert_eq!(true, x) / assert_eq!(false, x)"
			_kids: [
				{capture: "lhs", pattern: {node: "boolean_literal"}},
				{capture: "rhs"},
			]
		}).out
	}
}
