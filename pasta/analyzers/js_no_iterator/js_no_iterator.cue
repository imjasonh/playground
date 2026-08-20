// js_no_iterator flags __iterator__ property.
// ESLint `no-iterator` covers the same ground.

package js_no_iterator

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

js_no_iterator: schema.#Analyzer & {
	name:    "js_no_iterator"
	version: "0.1.0"
	doc:     "__iterator__ property"
	facts: {}
	rules: {
	js_no_iterator: _base & {
		name: "js_no_iterator"
		doc:  "__iterator__ property"
		requires: []
		provides: []
		match: {
			node: "member_expression"
			fields: {
				property: {capture: "prop", pattern: {node: "property_identifier"}}
			}
			where: [{op: "eq", args: ["@prop", "__iterator__"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "__iterator__ property"
		}
	}
	}
}
