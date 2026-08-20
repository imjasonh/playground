// js_no_new flags new used as a statement.
// ESLint `no-new` covers the same ground.

package js_no_new

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

js_no_new: schema.#Analyzer & {
	name:    "js_no_new"
	version: "0.1.0"
	doc:     "new used as a statement"
	facts: {}
	rules: {
	js_no_new: _base & {
		name: "js_no_new"
		doc:  "new used as a statement"
		requires: []
		provides: []
		match: {
			node: "expression_statement"
			children: [{node: "new_expression"}]
		}
		diagnose: {
			severity: "hint"
			message:  "new used as a statement"
		}
	}
	}
}
