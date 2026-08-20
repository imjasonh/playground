// js_no_ternary flags ternary expression.
// ESLint `no-ternary` covers the same ground.

package js_no_ternary

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

js_no_ternary: schema.#Analyzer & {
	name:    "js_no_ternary"
	version: "0.1.0"
	doc:     "ternary expression"
	facts: {}
	rules: {
	js_no_ternary: _base & {
		name: "js_no_ternary"
		doc:  "ternary expression"
		requires: []
		provides: []
		match: {
			node: "ternary_expression"
		}
		diagnose: {
			severity: "hint"
			message:  "ternary expression"
		}
	}
	}
}
