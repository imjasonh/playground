// js_no_cond_assign flags assignment used as if-condition.
// ESLint `no-cond-assign` covers the same ground.

package js_no_cond_assign

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

js_no_cond_assign: schema.#Analyzer & {
	name:    "js_no_cond_assign"
	version: "0.1.0"
	doc:     "assignment used as if-condition"
	facts: {}
	rules: {
	js_no_cond_assign_if: _base & {
		name: "js_no_cond_assign_if"
		doc:  "assignment used as if-condition"
		requires: []
		provides: []
		match: {
			node: "if_statement"
			fields: {
				condition: {
					node: "parenthesized_expression"
					children: [{capture: "inner", pattern: {node: "assignment_expression"}}]
				}
			}
		}
		diagnose: {
			severity: "warning"
			message:  "assignment used as if-condition"
		}
	}
	js_no_cond_assign_while: _base & {
		name: "js_no_cond_assign_while"
		doc:  "assignment used as while-condition"
		requires: []
		provides: []
		match: {
			node: "while_statement"
			fields: {
				condition: {
					node: "parenthesized_expression"
					children: [{capture: "inner", pattern: {node: "assignment_expression"}}]
				}
			}
		}
		diagnose: {
			severity: "warning"
			message:  "assignment used as while-condition"
		}
	}
	}
}
