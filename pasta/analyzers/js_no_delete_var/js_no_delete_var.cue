// js_no_delete_var flags delete of a variable.
// ESLint `no-delete-var` covers the same ground.

package js_no_delete_var

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

js_no_delete_var: schema.#Analyzer & {
	name:    "js_no_delete_var"
	version: "0.1.0"
	doc:     "delete of a variable"
	facts: {}
	rules: {
	js_no_delete_var: _base & {
		name: "js_no_delete_var"
		doc:  "delete of a variable"
		requires: []
		provides: []
		match: {
			node: "unary_expression"
			fields: {
				operator: {capture: "op"}
				argument: {capture: "arg", pattern: {node: "identifier"}}
			}
			where: [{op: "token_eq", args: ["@op", "delete"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "delete of a variable"
		}
	}
	}
}
