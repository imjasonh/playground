// js_no_negated_condition flags if-condition starts with ! and has an else.
// ESLint `no-negated-condition` covers the same ground.

package js_no_negated_condition

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

js_no_negated_condition: schema.#Analyzer & {
	name:    "js_no_negated_condition"
	version: "0.1.0"
	doc:     "if-condition starts with ! and has an else"
	facts: {}
	rules: {
	js_no_negated_condition: _base & {
		name: "js_no_negated_condition"
		doc:  "if-condition starts with ! and has an else"
		requires: []
		provides: []
		match: {
			node: "if_statement"
			fields: {
				condition: {
					node: "parenthesized_expression"
					children: [{capture: "inner", pattern: {node: "unary_expression"}}]
				}
				alternative: {node: "else_clause"}
			}
			where: [{op: "matches", args: ["@inner", "^!"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "if-condition starts with ! and has an else"
		}
	}
	}
}
