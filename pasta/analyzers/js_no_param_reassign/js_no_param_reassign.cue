// js_no_param_reassign flags assignment to a function parameter.
// ESLint `no-param-reassign` covers the same ground.

package js_no_param_reassign

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

js_no_param_reassign: schema.#Analyzer & {
	name:    "js_no_param_reassign"
	version: "0.1.0"
	doc:     "assignment to a function parameter"
	facts: {
		fn_param: {kind: "fn_param"}
	}
	rules: {

	mark_fn_param: _base & {
		name: "mark_fn_param"
		doc:  "Record identifier parameters"
		requires: []
		provides: ["fn_param"]
		match: {
			node: "formal_parameters"
			children: [{capture: "name", pattern: {node: "identifier"}}]
		}
		emit: [{fact: "fn_param", attach: "name"}]
	}
	js_no_param_reassign: _base & {
		name: "js_no_param_reassign"
		doc:  "assignment to a function parameter"
		requires: ["fn_param"]
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs", pattern: {node: "identifier"}}
			}
			where: [{op: "has_fact", args: ["@lhs", "fn_param"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "assignment to a function parameter"
		}
	}
	}
}
