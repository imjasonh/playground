// js_no_self_compare flags comparison where both sides are the same identifier.
// ESLint `no-self-compare` covers the same ground.

package js_no_self_compare

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_langs: [jslang.Name, tslang.Name, tsxlang.Name]

_base: {
	languages: _langs
}

js_no_self_compare: schema.#Analyzer & {
	name:    "js_no_self_compare"
	version: "0.1.0"
	doc:     "comparison where both sides are the same identifier"
	facts: {}
	rules: {
	js_no_self_compare: _base & {
		name: "js_no_self_compare"
		doc:  "comparison where both sides are the same identifier"
		requires: []
		provides: []
		match: {
			node: "binary_expression"
			fields: {
				left: {capture: "lhs", pattern: {node: "identifier"}}
				operator: {capture: "op"}
				right: {capture: "rhs", pattern: {node: "identifier"}}
			}
			where: [
				{op: "same_ident", args: ["@lhs", "@rhs"]},
				{op: "matches", args: ["@op", "^(===|!==|==|!=|<|<=|>|>=)$"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "comparison where both sides are the same identifier"
		}
	}
	}
}
