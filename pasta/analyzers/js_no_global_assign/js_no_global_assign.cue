// js_no_global_assign flags assignment to a read-only global.
// ESLint `no-global-assign` covers the same ground.

package js_no_global_assign

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

js_no_global_assign: schema.#Analyzer & {
	name:    "js_no_global_assign"
	version: "0.1.0"
	doc:     "assignment to a read-only global"
	facts: {}
	rules: {
	js_no_global_assign: _base & {
		name: "js_no_global_assign"
		doc:  "assignment to a read-only global"
		requires: []
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs"}
			}
			where: [{op: "matches", args: ["@lhs", "^(undefined|NaN|Infinity)$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "assignment to a read-only global"
		}
	}
	}
}
