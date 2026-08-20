// js_no_nonoctal_decimal_escape flags \8 or \9 escape in a string.
// ESLint `no-nonoctal-decimal-escape` covers the same ground.

package js_no_nonoctal_decimal_escape

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

js_no_nonoctal_decimal_escape: schema.#Analyzer & {
	name:    "js_no_nonoctal_decimal_escape"
	version: "0.1.0"
	doc:     "\\8 or \\9 escape in a string"
	facts: {}
	rules: {
	js_no_nonoctal_decimal_escape: _base & {
		name: "js_no_nonoctal_decimal_escape"
		doc:  "\\8 or \\9 escape in a string"
		requires: []
		provides: []
		match: {
			node: "string"
			where: [{op: "matches", args: ["@_root", "\\\\[89]"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "\\8 or \\9 escape in a string"
		}
	}
	}
}
