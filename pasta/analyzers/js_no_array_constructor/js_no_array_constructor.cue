// js_no_array_constructor flags new Array with multiple arguments.
// ESLint `no-array-constructor` covers the same ground.

package js_no_array_constructor

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

js_no_array_constructor: schema.#Analyzer & {
	name:    "js_no_array_constructor"
	version: "0.1.0"
	doc:     "new Array with multiple arguments"
	facts: {}
	rules: {
	js_no_array_constructor_new: _base & {
		name: "js_no_array_constructor_new"
		doc:  "new Array with multiple arguments"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor", pattern: {node: "identifier"}}
				arguments: {capture: "args", pattern: {node: "arguments"}}
			}
			where: [
				{op: "eq", args: ["@ctor", "Array"]},
				{op: "matches", args: ["@args", ","]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "new Array with multiple arguments"
		}
	}
	js_no_array_constructor_call: _base & {
		name: "js_no_array_constructor_call"
		doc:  "Array() call"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
			}
			where: [{op: "eq", args: ["@fn", "Array"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "Array() call"
		}
	}
	}
}
