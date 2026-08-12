// php_loose_equality rewrites `==` / `!=` to `===` / `!==`. PHP's
// loose equality coerces operand types in surprising ways
// (`"0" == false` is true; `"abc" == 0` was true before PHP 8).
// Strict equality compares without coercion.
//
// Comparisons against `null` are left alone: `$x == null` is a common
// nullish check that is not equivalent to `$x === null`.

package php_loose_equality

import (
	"github.com/imjasonh/pasta/schema"
	phplang "github.com/imjasonh/pasta/lang/php"
)

_eqRule: {
	_from: "==" | "!="
	_to:   "===" | "!=="

	out: {
		languages: [phplang.Name]
		requires: []
		provides: []

		match: {
			node: "binary_expression"
			fields: {
				left:     {capture: "left"}
				operator: {capture: "op"}
				right:    {capture: "right"}
			}
			where: [
				{op: "token_eq", args: ["@op", _from]},
				{op: "neq", args: ["@left", "null"]},
				{op: "neq", args: ["@right", "null"]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "use strict equality `\(_to)` instead of `\(_from)`"
		}

		rewrite: edits: [{
			target:      "op"
			replacement: _to
		}]
	}
}

php_loose_equality: schema.#Analyzer & {
	name:    "php_loose_equality"
	version: "0.1.0"
	doc:     "Replace == / != with === / !== (except null idioms)"
	facts: {}

	rules: {
		eq:  (_eqRule & {_from: "==", _to: "==="}).out & {name: "eq",  doc: "== -> ==="}
		neq: (_eqRule & {_from: "!=", _to: "!=="}).out & {name: "neq", doc: "!= -> !=="}
	}
}
