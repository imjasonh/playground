// js_no_new_func flags Function constructor.
// ESLint `no-new-func` covers the same ground.

package js_no_new_func

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

js_no_new_func: schema.#Analyzer & {
	name:    "js_no_new_func"
	version: "0.1.0"
	doc:     "Function constructor"
	facts: {}
	rules: {
	js_no_new_func: _base & {
		name: "js_no_new_func"
		doc:  "Function constructor"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor", pattern: {node: "identifier"}}
			}
			where: [{op: "eq", args: ["@ctor", "Function"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "Function constructor"
		}
	}
	js_no_func_ctor_call: _base & {
		name: "js_no_func_ctor_call"
		doc:  "Function() call"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
			}
			where: [{op: "eq", args: ["@fn", "Function"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "Function() call"
		}
	}
	}
}
