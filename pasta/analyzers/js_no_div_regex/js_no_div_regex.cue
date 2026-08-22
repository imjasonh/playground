// js_no_div_regex flags regex that starts with =.
// ESLint `no-div-regex` covers the same ground.

package js_no_div_regex

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

js_no_div_regex: schema.#Analyzer & {
	name:    "js_no_div_regex"
	version: "0.1.0"
	doc:     "regex that starts with ="
	facts: {}
	rules: {
	js_no_div_regex: _base & {
		name: "js_no_div_regex"
		doc:  "regex that starts with ="
		requires: []
		provides: []
		match: {
			node: "regex"
			where: [{op: "matches", args: ["@_root", "^=|/="]}]
		}
		diagnose: {
			severity: "hint"
			message:  "regex that starts with ="
		}
	}
	}
}
