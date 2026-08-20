// js_no_obj_calls flags calling a global object as a function.
// ESLint `no-obj-calls` covers the same ground.

package js_no_obj_calls

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

js_no_obj_calls: schema.#Analyzer & {
	name:    "js_no_obj_calls"
	version: "0.1.0"
	doc:     "calling a global object as a function"
	facts: {}
	rules: {
	js_no_obj_calls: _base & {
		name: "js_no_obj_calls"
		doc:  "calling a global object as a function"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
			}
			where: [{op: "matches", args: ["@fn", "^(Math|JSON|Reflect|Atomics|Intl)$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "calling a global object as a function"
		}
	}
	}
}
