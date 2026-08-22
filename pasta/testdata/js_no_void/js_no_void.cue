// js_no_void flags void operator.
// ESLint `no-void` covers the same ground.

package js_no_void

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

js_no_void: schema.#Analyzer & {
	name:    "js_no_void"
	version: "0.1.0"
	doc:     "void operator"
	facts: {}
	rules: {
	js_no_void: _base & {
		name: "js_no_void"
		doc:  "void operator"
		requires: []
		provides: []
		match: {
			node: "unary_expression"
			fields: {
				operator: {capture: "op"}
			}
			where: [{op: "token_eq", args: ["@op", "void"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "void operator"
		}
	}
	}
}
