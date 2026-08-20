// js_no_extra_bind flags .bind(this) on a function that does not use this.
// ESLint `no-extra-bind` covers the same ground.

package js_no_extra_bind

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

js_no_extra_bind: schema.#Analyzer & {
	name:    "js_no_extra_bind"
	version: "0.1.0"
	doc:     ".bind(this) on a function that does not use this"
	facts: {}
	rules: {
	js_no_extra_bind: _base & {
		name: "js_no_extra_bind"
		doc:  ".bind(this) on a function that does not use this"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						object: {capture: "obj"}
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
				arguments: {
					node: "arguments"
					children: [{capture: "thisarg", pattern: {node: "this"}}]
				}
			}
			where: [
				{op: "eq", args: ["@prop", "bind"]},
				{op: "subtree_lacks", args: ["@obj", "this"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  ".bind(this) on a function that does not use this"
		}
	}
	}
}
