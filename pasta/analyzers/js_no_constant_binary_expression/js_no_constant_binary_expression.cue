// js_no_constant_binary_expression flags binary expression whose both operands are literals.
// ESLint `no-constant-binary-expression` covers the same ground.

package js_no_constant_binary_expression

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

js_no_constant_binary_expression: schema.#Analyzer & {
	name:    "js_no_constant_binary_expression"
	version: "0.1.0"
	doc:     "binary expression whose both operands are literals"
	facts: {}
	rules: {
	js_no_constant_binary_expression: _base & {
		name: "js_no_constant_binary_expression"
		doc:  "binary expression whose both operands are literals"
		requires: []
		provides: []
		match: {
			node: "binary_expression"
			fields: {
				left: {capture: "left"}
				right: {capture: "right"}
			}
			where: [
				{op: "node_is", args: ["@left", ["true", "false", "number", "string", "null", "undefined"]]},
				{op: "node_is", args: ["@right", ["true", "false", "number", "string", "null", "undefined"]]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "binary expression whose both operands are literals"
		}
	}
	}
}
