// js_no_constant_condition flags constant if-condition.
// ESLint `no-constant-condition` covers the same ground.

package js_no_constant_condition

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

js_no_constant_condition: schema.#Analyzer & {
	name:    "js_no_constant_condition"
	version: "0.1.0"
	doc:     "constant if-condition"
	facts: {}
	rules: {
	js_no_constant_condition_if: _base & {
		name: "js_no_constant_condition_if"
		doc:  "constant if-condition"
		requires: []
		provides: []
		match: {
			node: "if_statement"
			fields: {
				condition: {
					node: "parenthesized_expression"
					children: [{capture: "inner"}]
				}
			}
			where: [{op: "node_is", args: ["@inner", ["true", "false", "number", "string", "null"]]}]
		}
		diagnose: {
			severity: "warning"
			message:  "constant if-condition"
		}
	}
	js_no_constant_condition_while: _base & {
		name: "js_no_constant_condition_while"
		doc:  "constant while-condition"
		requires: []
		provides: []
		match: {
			node: "while_statement"
			fields: {
				condition: {
					node: "parenthesized_expression"
					children: [{capture: "inner"}]
				}
			}
			where: [{op: "node_is", args: ["@inner", ["true", "false", "number", "string", "null"]]}]
		}
		diagnose: {
			severity: "warning"
			message:  "constant while-condition"
		}
	}
	}
}
