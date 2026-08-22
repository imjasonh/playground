// js_no_extra_boolean_cast flags double negation.
// ESLint `no-extra-boolean-cast` covers the same ground.

package js_no_extra_boolean_cast

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

js_no_extra_boolean_cast: schema.#Analyzer & {
	name:    "js_no_extra_boolean_cast"
	version: "0.1.0"
	doc:     "double negation"
	facts: {}
	rules: {
	js_no_extra_boolean_cast_bang: _base & {
		name: "js_no_extra_boolean_cast_bang"
		doc:  "double negation"
		requires: []
		provides: []
		match: {
			node: "unary_expression"
			fields: {
				operator: {capture: "op"}
				argument: {capture: "arg", pattern: {node: "unary_expression"}}
			}
			where: [
				{op: "token_eq", args: ["@op", "!"]},
				{op: "matches", args: ["@arg", "^!"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "double negation"
		}
	}
	js_no_extra_boolean_cast_boolean: _base & {
		name: "js_no_extra_boolean_cast_boolean"
		doc:  "Boolean() call"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {capture: "args", pattern: {node: "arguments"}}
			}
			where: [{op: "eq", args: ["@fn", "Boolean"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "Boolean() call"
		}
	}
	}
}
