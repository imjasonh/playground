// js_no_func_assign flags reassigning a function declaration.
// ESLint `no-func-assign` covers the same ground.

package js_no_func_assign

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

js_no_func_assign: schema.#Analyzer & {
	name:    "js_no_func_assign"
	version: "0.1.0"
	doc:     "reassigning a function declaration"
	facts: {
		fn_decl: {kind: "fn_decl"}
	}
	rules: {

	mark_fn_decl: _base & {
		name: "mark_fn_decl"
		doc:  "Record function-declaration names"
		requires: []
		provides: ["fn_decl"]
		match: {
			node: "function_declaration"
			fields: {
				name: {capture: "name", pattern: {node: "identifier"}}
			}
		}
		emit: [{fact: "fn_decl", attach: "name"}]
	}
	js_no_func_assign: _base & {
		name: "js_no_func_assign"
		doc:  "reassigning a function declaration"
		requires: ["fn_decl"]
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs", pattern: {node: "identifier"}}
			}
			where: [{op: "has_fact", args: ["@lhs", "fn_decl"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "reassigning a function declaration"
		}
	}
	}
}
