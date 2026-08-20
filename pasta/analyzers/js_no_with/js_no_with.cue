// js_no_with flags with statement.
// ESLint `no-with` covers the same ground.

package js_no_with

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

js_no_with: schema.#Analyzer & {
	name:    "js_no_with"
	version: "0.1.0"
	doc:     "with statement"
	facts: {}
	rules: {
	js_no_with: _base & {
		name: "js_no_with"
		doc:  "with statement"
		requires: []
		provides: []
		match: {
			node: "with_statement"
		}
		diagnose: {
			severity: "warning"
			message:  "with statement"
		}
	}
	}
}
