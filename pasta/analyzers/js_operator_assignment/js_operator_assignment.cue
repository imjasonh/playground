// js_operator_assignment flags x = x + y can be x += y.
// ESLint `operator-assignment` covers the same ground.

package js_operator_assignment

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

js_operator_assignment: schema.#Analyzer & {
	name:    "js_operator_assignment"
	version: "0.1.0"
	doc:     "x = x + y can be x += y"
	facts: {}
	rules: {
	js_operator_assignment: _base & {
		name: "js_operator_assignment"
		doc:  "x = x + y can be x += y"
		requires: []
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs", pattern: {node: "identifier"}}
				right: {
					node: "binary_expression"
					fields: {
						left: {capture: "blhs", pattern: {node: "identifier"}}
						operator: {capture: "op"}
						right: {capture: "brhs"}
					}
				}
			}
			where: [
				{op: "same_ident", args: ["@lhs", "@blhs"]},
				{op: "matches", args: ["@op", "^(\\+|\\-|\\*|\\/|%|\\*\\*)$"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "x = x + y can be x += y"
		}
	}
	}
}
