// js_no_implicit_coercion flags unary plus used as a number cast.
// ESLint `no-implicit-coercion` covers the same ground.

package js_no_implicit_coercion

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

js_no_implicit_coercion: schema.#Analyzer & {
	name:    "js_no_implicit_coercion"
	version: "0.1.0"
	doc:     "unary plus used as a number cast"
	facts: {}
	rules: {
	js_no_implicit_coercion_plus: _base & {
		name: "js_no_implicit_coercion_plus"
		doc:  "unary plus used as a number cast"
		requires: []
		provides: []
		match: {
			node: "unary_expression"
			fields: {
				operator: {capture: "op"}
				argument: {capture: "arg", pattern: {node: "identifier"}}
			}
			where: [{op: "token_eq", args: ["@op", "+"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "unary plus used as a number cast"
		}
	}
	}
}
