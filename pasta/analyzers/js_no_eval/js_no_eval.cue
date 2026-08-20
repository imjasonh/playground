// js_no_eval flags eval() call.
// ESLint `no-eval` covers the same ground.

package js_no_eval

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

js_no_eval: schema.#Analyzer & {
	name:    "js_no_eval"
	version: "0.1.0"
	doc:     "eval() call"
	facts: {}
	rules: {
	js_no_eval: _base & {
		name: "js_no_eval"
		doc:  "eval() call"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
			}
			where: [{op: "eq", args: ["@fn", "eval"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "eval() call"
		}
	}
	}
}
