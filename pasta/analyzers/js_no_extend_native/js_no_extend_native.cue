// js_no_extend_native flags assignment to a built-in prototype.
// ESLint `no-extend-native` covers the same ground.

package js_no_extend_native

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

js_no_extend_native: schema.#Analyzer & {
	name:    "js_no_extend_native"
	version: "0.1.0"
	doc:     "assignment to a built-in prototype"
	facts: {}
	rules: {
	js_no_extend_native: _base & {
		name: "js_no_extend_native"
		doc:  "assignment to a built-in prototype"
		requires: []
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs"}
			}
			where: [{op: "matches", args: ["@lhs", "^(Object|Array|Function|String|Number|Boolean|Date|RegExp|Promise|Map|Set|WeakMap|WeakSet|Error)\\.prototype\\."]}]
		}
		diagnose: {
			severity: "hint"
			message:  "assignment to a built-in prototype"
		}
	}
	}
}
