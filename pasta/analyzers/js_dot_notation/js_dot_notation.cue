// js_dot_notation flags use dot notation for a simple string key.
// ESLint `dot-notation` covers the same ground.

package js_dot_notation

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

js_dot_notation: schema.#Analyzer & {
	name:    "js_dot_notation"
	version: "0.1.0"
	doc:     "use dot notation for a simple string key"
	facts: {}
	rules: {
	js_dot_notation: _base & {
		name: "js_dot_notation"
		doc:  "use dot notation for a simple string key"
		requires: []
		provides: []
		match: {
			node: "subscript_expression"
			fields: {
				index: {capture: "idx", pattern: {node: "string"}}
			}
			where: [{op: "matches", args: ["@idx", "^['\"][A-Za-z_$][A-Za-z0-9_$]*['\"]$"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "use dot notation for a simple string key"
		}
	}
	}
}
