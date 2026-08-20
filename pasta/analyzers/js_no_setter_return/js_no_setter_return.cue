// js_no_setter_return flags setter returns a value.
// ESLint `no-setter-return` covers the same ground.

package js_no_setter_return

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

js_no_setter_return: schema.#Analyzer & {
	name:    "js_no_setter_return"
	version: "0.1.0"
	doc:     "setter returns a value"
	facts: {}
	rules: {
	js_no_setter_return: _base & {
		name: "js_no_setter_return"
		doc:  "setter returns a value"
		requires: []
		provides: []
		match: {
			node: "method_definition"
			fields: {
				body: {capture: "body"}
			}
			where: [
				{op: "matches", args: ["@_root", "(^|\\s)set\\s"]},
				{op: "matches", args: ["@body", "\\breturn\\s+\\S"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "setter returns a value"
		}
	}
	}
}
