// js_no_case_declarations flags lexical declaration in a case clause.
// ESLint `no-case-declarations` covers the same ground.

package js_no_case_declarations

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

js_no_case_declarations: schema.#Analyzer & {
	name:    "js_no_case_declarations"
	version: "0.1.0"
	doc:     "lexical declaration in a case clause"
	facts: {}
	rules: {
	js_no_case_declarations: _base & {
		name: "js_no_case_declarations"
		doc:  "lexical declaration in a case clause"
		requires: []
		provides: []
		match: {
			node: "switch_case"
			fields: {
				body: {capture: "body", pattern: {node: ["lexical_declaration", "function_declaration", "class_declaration"]}}
			}
		}
		diagnose: {
			severity: "warning"
			message:  "lexical declaration in a case clause"
		}
	}
	}
}
