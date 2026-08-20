// js_prefer_numeric_literals flags parseInt of a string with radix 2/8/16.
// ESLint `prefer-numeric-literals` covers the same ground.

package js_prefer_numeric_literals

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

js_prefer_numeric_literals: schema.#Analyzer & {
	name:    "js_prefer_numeric_literals"
	version: "0.1.0"
	doc:     "parseInt of a string with radix 2/8/16"
	facts: {}
	rules: {
	js_prefer_numeric_literals: _base & {
		name: "js_prefer_numeric_literals"
		doc:  "parseInt of a string with radix 2/8/16"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {
					node: "arguments"
					children: [
						{node: "string"},
						{capture: "radix", pattern: {node: "number"}},
					]
				}
			}
			where: [
				{op: "eq", args: ["@fn", "parseInt"]},
				{op: "matches", args: ["@radix", "^(2|8|16)$"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "parseInt of a string with radix 2/8/16"
		}
	}
	}
}
