// js_init_declarations flags let/const/var without an initializer.
// ESLint `init-declarations` covers the same ground.

package js_init_declarations

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

js_init_declarations: schema.#Analyzer & {
	name:    "js_init_declarations"
	version: "0.1.0"
	doc:     "let/const/var without an initializer"
	facts: {}
	rules: {
	js_init_declarations: _base & {
		name: "js_init_declarations"
		doc:  "let/const/var without an initializer"
		requires: []
		provides: []
		match: {
			node: "variable_declarator"
			fields: {
				name: {capture: "name"}
			}
			absent_fields: ["value"]
		}
		diagnose: {
			severity: "hint"
			message:  "let/const/var without an initializer"
		}
	}
	}
}
