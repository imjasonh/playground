// js_no_return_assign flags assignment in a return statement.
// ESLint `no-return-assign` covers the same ground.

package js_no_return_assign

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

js_no_return_assign: schema.#Analyzer & {
	name:    "js_no_return_assign"
	version: "0.1.0"
	doc:     "assignment in a return statement"
	facts: {}
	rules: {
	js_no_return_assign: _base & {
		name: "js_no_return_assign"
		doc:  "assignment in a return statement"
		requires: []
		provides: []
		match: {
			node: "return_statement"
			children: [{node: "assignment_expression"}]
		}
		diagnose: {
			severity: "hint"
			message:  "assignment in a return statement"
		}
	}
	}
}
