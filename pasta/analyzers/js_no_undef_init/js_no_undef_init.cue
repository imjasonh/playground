// js_no_undef_init flags initialized to undefined.
// ESLint `no-undef-init` covers the same ground.

package js_no_undef_init

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

js_no_undef_init: schema.#Analyzer & {
	name:    "js_no_undef_init"
	version: "0.1.0"
	doc:     "initialized to undefined"
	facts: {}
	rules: {
	js_no_undef_init: _base & {
		name: "js_no_undef_init"
		doc:  "initialized to undefined"
		requires: []
		provides: []
		match: {
			node: "variable_declarator"
			fields: {
				value: {capture: "val", pattern: {node: "undefined"}}
			}
		}
		diagnose: {
			severity: "hint"
			message:  "initialized to undefined"
		}
	}
	}
}
