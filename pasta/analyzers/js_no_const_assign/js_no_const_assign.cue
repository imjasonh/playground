// js_no_const_assign flags assignment to a const binding.
// ESLint `no-const-assign` covers the same ground.

package js_no_const_assign

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

js_no_const_assign: schema.#Analyzer & {
	name:    "js_no_const_assign"
	version: "0.1.0"
	doc:     "assignment to a const binding"
	facts: {
		const_bind: {kind: "const_bind"}
	}
	rules: {

	mark_const: _base & {
		name: "mark_const"
		doc:  "Record const binding names"
		requires: []
		provides: ["const_bind"]
		match: {
			node: "lexical_declaration"
			fields: {
				kind: {capture: "kind"}
			}
			children: [{
				node: "variable_declarator"
				fields: {
					name: {capture: "name", pattern: {node: "identifier"}}
				}
			}]
			where: [{op: "token_eq", args: ["@kind", "const"]}]
		}
		emit: [{fact: "const_bind", attach: "name"}]
	}
	js_no_const_assign: _base & {
		name: "js_no_const_assign"
		doc:  "assignment to a const binding"
		requires: ["const_bind"]
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs", pattern: {node: "identifier"}}
			}
			where: [{op: "has_fact", args: ["@lhs", "const_bind"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "assignment to a const binding"
		}
	}
	}
}
