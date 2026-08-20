// js_prefer_spread flags .apply(undefined/null/obj, args) instead of spread.
// ESLint `prefer-spread` covers the same ground.

package js_prefer_spread

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

js_prefer_spread: schema.#Analyzer & {
	name:    "js_prefer_spread"
	version: "0.1.0"
	doc:     ".apply(undefined/null/obj, args) instead of spread"
	facts: {}
	rules: {
	js_prefer_spread: _base & {
		name: "js_prefer_spread"
		doc:  ".apply(undefined/null/obj, args) instead of spread"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
				arguments: {
					node: "arguments"
					children: [
						{node: ["undefined", "null", "identifier"]},
						{capture: "args", pattern: {node: "identifier"}},
					]
				}
			}
			where: [{op: "eq", args: ["@prop", "apply"]}]
		}
		diagnose: {
			severity: "hint"
			message:  ".apply(undefined/null/obj, args) instead of spread"
		}
	}
	}
}
