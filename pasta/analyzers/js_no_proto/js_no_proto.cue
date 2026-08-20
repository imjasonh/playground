// js_no_proto flags __proto__ property.
// ESLint `no-proto` covers the same ground.

package js_no_proto

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

js_no_proto: schema.#Analyzer & {
	name:    "js_no_proto"
	version: "0.1.0"
	doc:     "__proto__ property"
	facts: {}
	rules: {
	js_no_proto: _base & {
		name: "js_no_proto"
		doc:  "__proto__ property"
		requires: []
		provides: []
		match: {
			node: "member_expression"
			fields: {
				property: {capture: "prop", pattern: {node: "property_identifier"}}
			}
			where: [{op: "eq", args: ["@prop", "__proto__"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "__proto__ property"
		}
	}
	}
}
