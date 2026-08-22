// js_no_multi_assign flags chained assignment.
// ESLint `no-multi-assign` covers the same ground.

package js_no_multi_assign

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

js_no_multi_assign: schema.#Analyzer & {
	name:    "js_no_multi_assign"
	version: "0.1.0"
	doc:     "chained assignment"
	facts: {}
	rules: {
	js_no_multi_assign: _base & {
		name: "js_no_multi_assign"
		doc:  "chained assignment"
		requires: []
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				right: {capture: "rhs", pattern: {node: "assignment_expression"}}
			}
		}
		diagnose: {
			severity: "hint"
			message:  "chained assignment"
		}
	}
	}
}
