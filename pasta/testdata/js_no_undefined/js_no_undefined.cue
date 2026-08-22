// js_no_undefined flags undefined identifier.
// ESLint `no-undefined` covers the same ground.

package js_no_undefined

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

js_no_undefined: schema.#Analyzer & {
	name:    "js_no_undefined"
	version: "0.1.0"
	doc:     "undefined identifier"
	facts: {}
	rules: {
	js_no_undefined: _base & {
		name: "js_no_undefined"
		doc:  "undefined identifier"
		requires: []
		provides: []
		match: {
			node: "undefined"
		}
		diagnose: {
			severity: "hint"
			message:  "undefined identifier"
		}
	}
	}
}
