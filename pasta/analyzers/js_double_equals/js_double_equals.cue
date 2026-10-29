// js_double_equals rewrites `==` / `!=` to `===` / `!==` in JavaScript
// and TypeScript. JavaScript's loose equality coerces operand types,
// which is almost always surprising; the strict variants compare
// without coercion. ESLint's `eqeqeq` covers the same ground. Google
// JS and TS style require `===` / `!==`, with `== null` left as the
// nullish check.
//
// Comparisons against `null` / `undefined` are left alone: `x == null`
// is an idiomatic "nullish" check that is *not* equivalent to
// `x === null`.

package js_double_equals

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_eqRule: {
	_from: "==" | "!="
	_to:   "===" | "!=="

	out: {
		languages: [jslang.Name, tslang.Name, tsxlang.Name]
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
				// Skip nullish idioms: `x == null` / `x != undefined`.
				{op: "neq", args: ["@left", "null"]},
				{op: "neq", args: ["@left", "undefined"]},
				{op: "neq", args: ["@right", "null"]},
				{op: "neq", args: ["@right", "undefined"]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "use strict equality `\(_to)` instead of `\(_from)`"
		}

		// Surgical: replace only the operator token. Operand bytes
		// (and any comments around them) are untouched.
		rewrite: edits: [{
			target:      "op"
			replacement: _to
		}]
	}
}

js_double_equals: schema.#Analyzer & {
	name:    "js_double_equals"
	version: "0.1.0"
	doc:     "Replace == / != with === / !== (except null/undefined idioms)"
	facts: {}

	rules: {
		eq:  (_eqRule & {_from: "==", _to: "==="}).out & {name: "eq",  doc: "== -> ==="}
		neq: (_eqRule & {_from: "!=", _to: "!=="}).out & {name: "neq", doc: "!= -> !=="}
	}
}
