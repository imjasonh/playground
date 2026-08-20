// js_no_alert flags alert / confirm / prompt.
// ESLint `no-alert` covers the same ground.

package js_no_alert

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

js_no_alert: schema.#Analyzer & {
	name:    "js_no_alert"
	version: "0.1.0"
	doc:     "alert / confirm / prompt"
	facts: {}
	rules: {
	js_no_alert: _base & {
		name: "js_no_alert"
		doc:  "alert / confirm / prompt"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
			}
			where: [{op: "matches", args: ["@fn", "^(alert|confirm|prompt)$"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "alert / confirm / prompt"
		}
	}
	}
}
