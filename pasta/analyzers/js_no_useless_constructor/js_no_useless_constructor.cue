// js_no_useless_constructor flags empty constructor in a class that does not extend.
// ESLint `no-useless-constructor` covers the same ground.

package js_no_useless_constructor

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

js_no_useless_constructor: schema.#Analyzer & {
	name:    "js_no_useless_constructor"
	version: "0.1.0"
	doc:     "empty constructor in a class that does not extend"
	facts: {}
	rules: {
	js_no_useless_constructor: _base & {
		name: "js_no_useless_constructor"
		doc:  "empty constructor in a class that does not extend"
		requires: []
		provides: []
		match: {
			node: "class_declaration"
			fields: {
				body: {
					node: "class_body"
					fields: {
						member: {
							capture: "ctor"
							pattern: {
								node: "method_definition"
								fields: {
									name: {capture: "name", pattern: {node: "property_identifier"}}
									body: {capture: "body", pattern: {node: "statement_block"}}
								}
							}
						}
					}
				}
			}
			where: [
				{op: "eq", args: ["@name", "constructor"]},
				{op: "empty", args: ["@body"]},
				{op: "not_matches", args: ["@_root", "\\bextends\\b"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "empty constructor in a class that does not extend"
		}
	}
	}
}
