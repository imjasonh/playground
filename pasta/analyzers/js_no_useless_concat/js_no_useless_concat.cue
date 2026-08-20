// js_no_useless_concat flags concatenation of two string literals.
// ESLint `no-useless-concat` covers the same ground.

package js_no_useless_concat

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

js_no_useless_concat: schema.#Analyzer & {
	name:    "js_no_useless_concat"
	version: "0.1.0"
	doc:     "concatenation of two string literals"
	facts: {}
	rules: {
	js_no_useless_concat: _base & {
		name: "js_no_useless_concat"
		doc:  "concatenation of two string literals"
		requires: []
		provides: []
		match: {
			node: "binary_expression"
			fields: {
				left: {capture: "left", pattern: {node: "string"}}
				operator: {capture: "op"}
				right: {capture: "right", pattern: {node: "string"}}
			}
			where: [{op: "token_eq", args: ["@op", "+"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "concatenation of two string literals"
		}
	}
	}
}
