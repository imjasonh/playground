// js_constructor_super flags subclass constructor must call super().
// ESLint `constructor-super` covers the same ground.

package js_constructor_super

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

js_constructor_super: schema.#Analyzer & {
	name:    "js_constructor_super"
	version: "0.1.0"
	doc:     "subclass constructor must call super()"
	facts: {}
	rules: {
	js_constructor_super: _base & {
		name: "js_constructor_super"
		doc:  "subclass constructor must call super()"
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
									body: {capture: "body"}
								}
							}
						}
					}
				}
			}
			where: [
				{op: "eq", args: ["@name", "constructor"]},
				{op: "subtree_lacks", args: ["@body", "super"]},
				{op: "matches", args: ["@_root", "\\bextends\\b"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "subclass constructor must call super()"
		}
	}
	}
}
