// js_no_implied_eval flags setTimeout/setInterval with a string.
// ESLint `no-implied-eval` covers the same ground.

package js_no_implied_eval

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

js_no_implied_eval: schema.#Analyzer & {
	name:    "js_no_implied_eval"
	version: "0.1.0"
	doc:     "setTimeout/setInterval with a string"
	facts: {}
	rules: {
	js_no_implied_eval_timer: _base & {
		name: "js_no_implied_eval_timer"
		doc:  "setTimeout/setInterval with a string"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {
					node: "arguments"
					children: [{capture: "first", pattern: {node: "string"}}]
				}
			}
			where: [{op: "matches", args: ["@fn", "^(setTimeout|setInterval|execScript)$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "setTimeout/setInterval with a string"
		}
	}
	}
}
