// js_one_var flags multiple declarators in one declaration.
// ESLint `one-var` covers the same ground.

package js_one_var

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

js_one_var: schema.#Analyzer & {
	name:    "js_one_var"
	version: "0.1.0"
	doc:     "multiple declarators in one declaration"
	facts: {}
	rules: {
	js_one_var: _base & {
		name: "js_one_var"
		doc:  "multiple declarators in one declaration"
		requires: []
		provides: []
		match: {
			node: ["variable_declaration", "lexical_declaration"]
			children: [{node: "variable_declarator"}, {node: "variable_declarator"}]
		}
		diagnose: {
			severity: "hint"
			message:  "multiple declarators in one declaration"
		}
	}
	}
}
