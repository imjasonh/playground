// js_no_constructor_return flags constructor returns a value.
// ESLint `no-constructor-return` covers the same ground.

package js_no_constructor_return

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

js_no_constructor_return: schema.#Analyzer & {
	name:    "js_no_constructor_return"
	version: "0.1.0"
	doc:     "constructor returns a value"
	facts: {}
	rules: {
	js_no_constructor_return: _base & {
		name: "js_no_constructor_return"
		doc:  "constructor returns a value"
		requires: []
		provides: []
		match: {
			node: "method_definition"
			fields: {
				name: {capture: "name", pattern: {node: "property_identifier"}}
				body: {capture: "body"}
			}
			where: [
				{op: "eq", args: ["@name", "constructor"]},
				{op: "matches", args: ["@body", "\\breturn\\s+\\S"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "constructor returns a value"
		}
	}
	}
}
