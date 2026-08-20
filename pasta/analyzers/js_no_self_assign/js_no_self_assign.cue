// js_no_self_assign flags assignment where both sides are the same identifier.
// ESLint `no-self-assign` covers the same ground.

package js_no_self_assign

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

js_no_self_assign: schema.#Analyzer & {
	name:    "js_no_self_assign"
	version: "0.1.0"
	doc:     "assignment where both sides are the same identifier"
	facts: {}
	rules: {
	js_no_self_assign: _base & {
		name: "js_no_self_assign"
		doc:  "assignment where both sides are the same identifier"
		requires: []
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs", pattern: {node: "identifier"}}
				right: {capture: "rhs", pattern: {node: "identifier"}}
			}
			where: [{op: "same_ident", args: ["@lhs", "@rhs"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "assignment where both sides are the same identifier"
		}
	}
	}
}
