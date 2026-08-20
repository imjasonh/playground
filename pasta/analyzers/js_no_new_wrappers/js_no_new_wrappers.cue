// js_no_new_wrappers flags new String/Number/Boolean.
// ESLint `no-new-wrappers` covers the same ground.

package js_no_new_wrappers

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

js_no_new_wrappers: schema.#Analyzer & {
	name:    "js_no_new_wrappers"
	version: "0.1.0"
	doc:     "new String/Number/Boolean"
	facts: {}
	rules: {
	js_no_new_wrappers: _base & {
		name: "js_no_new_wrappers"
		doc:  "new String/Number/Boolean"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor", pattern: {node: "identifier"}}
			}
			where: [{op: "matches", args: ["@ctor", "^(String|Number|Boolean)$"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "new String/Number/Boolean"
		}
	}
	}
}
