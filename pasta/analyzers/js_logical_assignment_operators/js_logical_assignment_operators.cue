// js_logical_assignment_operators flags x = x && y can be x &&= y.
// ESLint `logical-assignment-operators` covers the same ground.

package js_logical_assignment_operators

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

js_logical_assignment_operators: schema.#Analyzer & {
	name:    "js_logical_assignment_operators"
	version: "0.1.0"
	doc:     "x = x && y can be x &&= y"
	facts: {}
	rules: {
	js_logical_assignment_operators: _base & {
		name: "js_logical_assignment_operators"
		doc:  "x = x && y can be x &&= y"
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
				{op: "matches", args: ["@op", "^(&&|\\|\\||\\?\\?)$"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "x = x && y can be x &&= y"
		}
	}
	}
}
