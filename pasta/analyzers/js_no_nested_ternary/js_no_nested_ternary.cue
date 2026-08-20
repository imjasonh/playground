// js_no_nested_ternary flags ternary nested in a ternary.
// ESLint `no-nested-ternary` covers the same ground.

package js_no_nested_ternary

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

js_no_nested_ternary: schema.#Analyzer & {
	name:    "js_no_nested_ternary"
	version: "0.1.0"
	doc:     "ternary nested in a ternary"
	facts: {}
	rules: {
	js_no_nested_ternary: _base & {
		name: "js_no_nested_ternary"
		doc:  "ternary nested in a ternary"
		requires: []
		provides: []
		match: {
			node: "ternary_expression"
			fields: {
				alternative: {capture: "alt"}
				consequence: {capture: "cons"}
			}
			where: [{op: "node_is", args: ["@alt", "ternary_expression"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "ternary nested in a ternary"
		}
	}
	}
}
