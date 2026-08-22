// js_no_continue flags continue statement.
// ESLint `no-continue` covers the same ground.

package js_no_continue

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

js_no_continue: schema.#Analyzer & {
	name:    "js_no_continue"
	version: "0.1.0"
	doc:     "continue statement"
	facts: {}
	rules: {
	js_no_continue: _base & {
		name: "js_no_continue"
		doc:  "continue statement"
		requires: []
		provides: []
		match: {
			node: "continue_statement"
		}
		diagnose: {
			severity: "hint"
			message:  "continue statement"
		}
	}
	}
}
