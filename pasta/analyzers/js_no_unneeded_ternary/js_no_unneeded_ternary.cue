// js_no_unneeded_ternary flags ternary that should be a boolean or ||.
// ESLint `no-unneeded-ternary` covers the same ground.

package js_no_unneeded_ternary

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

js_no_unneeded_ternary: schema.#Analyzer & {
	name:    "js_no_unneeded_ternary"
	version: "0.1.0"
	doc:     "ternary that should be a boolean or ||"
	facts: {}
	rules: {
	js_no_unneeded_ternary: _base & {
		name: "js_no_unneeded_ternary"
		doc:  "ternary that should be a boolean or ||"
		requires: []
		provides: []
		match: {
			node: "ternary_expression"
			fields: {
				condition: {capture: "cond", pattern: {node: "identifier"}}
				consequence: {capture: "cons"}
				alternative: {capture: "alt"}
			}
			where: [
				{op: "node_is", args: ["@cons", "true"]},
				{op: "node_is", args: ["@alt", "false"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "ternary that should be a boolean or ||"
		}
	}
	js_no_unneeded_ternary_same: _base & {
		name: "js_no_unneeded_ternary_same"
		doc:  "x ? x : y"
		requires: []
		provides: []
		match: {
			node: "ternary_expression"
			fields: {
				condition: {capture: "cond", pattern: {node: "identifier"}}
				consequence: {capture: "cons", pattern: {node: "identifier"}}
				alternative: {capture: "alt"}
			}
			where: [{op: "same_ident", args: ["@cond", "@cons"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "x ? x : y"
		}
	}
	}
}
