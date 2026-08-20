// js_guard_for_in flags for-in body is not guarded by an if.
// ESLint `guard-for-in` covers the same ground.

package js_guard_for_in

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

js_guard_for_in: schema.#Analyzer & {
	name:    "js_guard_for_in"
	version: "0.1.0"
	doc:     "for-in body is not guarded by an if"
	facts: {}
	rules: {
	js_guard_for_in: _base & {
		name: "js_guard_for_in"
		doc:  "for-in body is not guarded by an if"
		requires: []
		provides: []
		match: {
			node: "for_in_statement"
			fields: {
				operator: {capture: "op"}
				body: {capture: "body"}
			}
			where: [
				{op: "token_eq", args: ["@op", "in"]},
				{op: "node_is_not", args: ["@body", "if_statement"]},
				{op: "not_matches", args: ["@body", "^\\{\\s*if\\b"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "for-in body is not guarded by an if"
		}
	}
	}
}
