// rust_almost_complete_range rewrites half-open char ranges that are
// one endpoint short of a complete class:
//
//   'a'..'z'  ->  'a'..='z'
//   'A'..'Z'  ->  'A'..='Z'
//   '0'..'9'  ->  '0'..='9'
//
// Clippy `almost_complete_range` covers the same ground. Inclusive
// `..=` forms are already complete and are left alone.

package rust_almost_complete_range

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

_charRange: {
	_lo: string
	_hi: string

	out: {
		languages: [rustlang.Name]
		requires: []
		provides: []

		match: {
			node: "range_expression"
			children: [
				{capture: "start", pattern: {node: "char_literal"}},
				{capture: "end", pattern: {node: "char_literal"}},
			]
			where: [
				{op: "eq", args: ["@start", _lo]},
				{op: "eq", args: ["@end", _hi]},
				{op: "not_matches", args: ["@_root", "="]},
			]
		}

		diagnose: {
			severity: "hint"
			message:  "`\(_lo)..\(_hi)` is almost a complete range; use `\(_lo)..=\(_hi)`"
		}

		rewrite: edits: [{
			target:      "_root"
			replacement: "\(_lo)..=\(_hi)"
		}]
	}
}

rust_almost_complete_range: schema.#Analyzer & {
	name:    "rust_almost_complete_range"
	version: "0.1.0"
	doc:     "Rewrite 'a'..'z' to 'a'..='z' (clippy almost_complete_range)"
	facts: {}

	rules: {
		az: (_charRange & {_lo: "'a'", _hi: "'z'"}).out & {
			name: "az"
			doc:  "'a'..'z' -> 'a'..='z'"
		}
		AZ: (_charRange & {_lo: "'A'", _hi: "'Z'"}).out & {
			name: "upper_az"
			doc:  "'A'..'Z' -> 'A'..='Z'"
		}
		digits: (_charRange & {_lo: "'0'", _hi: "'9'"}).out & {
			name: "digits"
			doc:  "'0'..'9' -> '0'..='9'"
		}
	}
}
