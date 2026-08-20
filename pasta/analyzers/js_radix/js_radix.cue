// js_radix flags parseInt without a radix.
// ESLint `radix` covers the same ground.

package js_radix

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

js_radix: schema.#Analyzer & {
	name:    "js_radix"
	version: "0.1.0"
	doc:     "parseInt without a radix"
	facts: {}
	rules: {
	js_radix: _base & {
		name: "js_radix"
		doc:  "parseInt without a radix"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {capture: "args", pattern: {node: "arguments"}}
			}
			where: [
				{op: "eq", args: ["@fn", "parseInt"]},
				{op: "named_child_count", args: ["@args", "1"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "parseInt without a radix"
		}
	}
	}
}
