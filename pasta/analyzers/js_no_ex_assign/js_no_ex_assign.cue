// js_no_ex_assign flags reassigning a catch binding.
// ESLint `no-ex-assign` covers the same ground.

package js_no_ex_assign

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

js_no_ex_assign: schema.#Analyzer & {
	name:    "js_no_ex_assign"
	version: "0.1.0"
	doc:     "reassigning a catch binding"
	facts: {}
	rules: {
	js_no_ex_assign: _base & {
		name: "js_no_ex_assign"
		doc:  "reassigning a catch binding"
		requires: []
		provides: []
		match: {
			node: "catch_clause"
			fields: {
				parameter: {capture: "param", pattern: {node: "identifier"}}
				body: {
					node: "statement_block"
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
			}
			where: [{op: "same_ident", args: ["@param", "@lhs"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "reassigning a catch binding"
		}
	}
	}
}
