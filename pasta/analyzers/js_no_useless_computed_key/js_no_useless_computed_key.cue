// js_no_useless_computed_key flags computed key that is a literal identifier-like string.
// ESLint `no-useless-computed-key` covers the same ground.

package js_no_useless_computed_key

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

js_no_useless_computed_key: schema.#Analyzer & {
	name:    "js_no_useless_computed_key"
	version: "0.1.0"
	doc:     "computed key that is a literal identifier-like string"
	facts: {}
	rules: {
	js_no_useless_computed_key: _base & {
		name: "js_no_useless_computed_key"
		doc:  "computed key that is a literal identifier-like string"
		requires: []
		provides: []
		match: {
			node: "pair"
			fields: {
				key: {
					node: "computed_property_name"
					children: [{capture: "inner", pattern: {node: "string"}}]
				}
			}
			where: [{op: "matches", args: ["@inner", "^['\"][A-Za-z_$][A-Za-z0-9_$]*['\"]$"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "computed key that is a literal identifier-like string"
		}
	}
	}
}
