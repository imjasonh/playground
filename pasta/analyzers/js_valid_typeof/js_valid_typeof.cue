// js_valid_typeof flags typeof compared to an invalid string.
// ESLint `valid-typeof` covers the same ground.

package js_valid_typeof

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

js_valid_typeof: schema.#Analyzer & {
	name:    "js_valid_typeof"
	version: "0.1.0"
	doc:     "typeof compared to an invalid string"
	facts: {}
	rules: {
	js_valid_typeof: _base & {
		name: "js_valid_typeof"
		doc:  "typeof compared to an invalid string"
		requires: []
		provides: []
		match: {
			node: "binary_expression"
			fields: {
				left: {capture: "left", pattern: {node: "unary_expression"}}
				operator: {capture: "op"}
				right: {capture: "right", pattern: {node: "string"}}
			}
			where: [
				{op: "matches", args: ["@left", "^typeof\\b"]},
				{op: "matches", args: ["@op", "^(===|!==|==|!=)$"]},
				{op: "not_matches", args: ["@right", "^['\"](undefined|object|boolean|number|string|function|symbol|bigint)['\"]$"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "typeof compared to an invalid string"
		}
	}
	}
}
