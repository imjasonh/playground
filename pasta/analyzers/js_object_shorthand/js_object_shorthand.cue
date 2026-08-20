// js_object_shorthand flags object property that can be shorthand.
// ESLint `object-shorthand` covers the same ground.

package js_object_shorthand

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

js_object_shorthand: schema.#Analyzer & {
	name:    "js_object_shorthand"
	version: "0.1.0"
	doc:     "object property that can be shorthand"
	facts: {}
	rules: {
	js_object_shorthand: _base & {
		name: "js_object_shorthand"
		doc:  "object property that can be shorthand"
		requires: []
		provides: []
		match: {
			node: "pair"
			fields: {
				key: {capture: "key", pattern: {node: "property_identifier"}}
				value: {capture: "val", pattern: {node: "identifier"}}
			}
			where: [{op: "same_ident", args: ["@key", "@val"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "object property that can be shorthand"
		}
	}
	}
}
