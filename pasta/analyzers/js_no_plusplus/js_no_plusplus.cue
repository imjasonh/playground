// js_no_plusplus flags ++ or --.
// ESLint `no-plusplus` covers the same ground.

package js_no_plusplus

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

js_no_plusplus: schema.#Analyzer & {
	name:    "js_no_plusplus"
	version: "0.1.0"
	doc:     "++ or --"
	facts: {}
	rules: {
	js_no_plusplus: _base & {
		name: "js_no_plusplus"
		doc:  "++ or --"
		requires: []
		provides: []
		match: {
			node: "update_expression"
		}
		diagnose: {
			severity: "hint"
			message:  "++ or --"
		}
	}
	}
}
