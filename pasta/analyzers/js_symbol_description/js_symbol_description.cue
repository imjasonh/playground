// js_symbol_description flags Symbol() without a description.
// ESLint `symbol-description` covers the same ground.

package js_symbol_description

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

js_symbol_description: schema.#Analyzer & {
	name:    "js_symbol_description"
	version: "0.1.0"
	doc:     "Symbol() without a description"
	facts: {}
	rules: {
	js_symbol_description: _base & {
		name: "js_symbol_description"
		doc:  "Symbol() without a description"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {capture: "args", pattern: {node: "arguments"}}
			}
			where: [
				{op: "eq", args: ["@fn", "Symbol"]},
				{op: "empty", args: ["@args"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "Symbol() without a description"
		}
	}
	}
}
