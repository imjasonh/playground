// js_no_implicit_globals flags top-level assignment to an identifier.
// ESLint `no-implicit-globals` covers the same ground.

package js_no_implicit_globals

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

js_no_implicit_globals: schema.#Analyzer & {
	name:    "js_no_implicit_globals"
	version: "0.1.0"
	doc:     "top-level assignment to an identifier"
	facts: {}
	rules: {
	js_no_implicit_globals: _base & {
		name: "js_no_implicit_globals"
		doc:  "top-level assignment to an identifier"
		requires: []
		provides: []
		match: {
			node: "program"
			adjacent: [{
				node: "expression_statement"
				children: [{
					node: "assignment_expression"
					fields: {
						left: {capture: "lhs", pattern: {node: "identifier"}}
					}
				}]
			}]
		}
		diagnose: {
			severity: "hint"
			message:  "top-level assignment to an identifier"
		}
	}
	}
}
