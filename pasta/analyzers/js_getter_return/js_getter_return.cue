// js_getter_return flags getter body has no return.
// ESLint `getter-return` covers the same ground.

package js_getter_return

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

js_getter_return: schema.#Analyzer & {
	name:    "js_getter_return"
	version: "0.1.0"
	doc:     "getter body has no return"
	facts: {}
	rules: {
	js_getter_return: _base & {
		name: "js_getter_return"
		doc:  "getter body has no return"
		requires: []
		provides: []
		match: {
			node: "method_definition"
			fields: {
				body: {capture: "body"}
				name: {capture: "name"}
			}
			where: [
				{op: "matches", args: ["@_root", "(^|\\s)get\\s"]},
				{op: "subtree_lacks", args: ["@body", "return_statement"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "getter body has no return"
		}
	}
	}
}
