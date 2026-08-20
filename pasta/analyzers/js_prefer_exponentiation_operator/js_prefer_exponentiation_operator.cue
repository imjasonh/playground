// js_prefer_exponentiation_operator flags Math.pow instead of **.
// ESLint `prefer-exponentiation-operator` covers the same ground.

package js_prefer_exponentiation_operator

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

js_prefer_exponentiation_operator: schema.#Analyzer & {
	name:    "js_prefer_exponentiation_operator"
	version: "0.1.0"
	doc:     "Math.pow instead of **"
	facts: {}
	rules: {
	js_prefer_exponentiation_operator: _base & {
		name: "js_prefer_exponentiation_operator"
		doc:  "Math.pow instead of **"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						object: {capture: "obj", pattern: {node: "identifier"}}
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
			}
			where: [
				{op: "eq", args: ["@obj", "Math"]},
				{op: "eq", args: ["@prop", "pow"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "Math.pow instead of **"
		}
	}
	}
}
