// js_no_octal flags legacy octal literal.
// ESLint `no-octal` covers the same ground.

package js_no_octal

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

js_no_octal: schema.#Analyzer & {
	name:    "js_no_octal"
	version: "0.1.0"
	doc:     "legacy octal literal"
	facts: {}
	rules: {
	js_no_octal: _base & {
		name: "js_no_octal"
		doc:  "legacy octal literal"
		requires: []
		provides: []
		match: {
			node: "number"
			where: [{op: "matches", args: ["@_root", "^0[0-7]+$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "legacy octal literal"
		}
	}
	}
}
