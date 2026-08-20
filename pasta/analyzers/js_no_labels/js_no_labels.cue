// js_no_labels flags labeled statement.
// ESLint `no-labels` covers the same ground.

package js_no_labels

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

js_no_labels: schema.#Analyzer & {
	name:    "js_no_labels"
	version: "0.1.0"
	doc:     "labeled statement"
	facts: {}
	rules: {
	js_no_labels: _base & {
		name: "js_no_labels"
		doc:  "labeled statement"
		requires: []
		provides: []
		match: {
			node: "labeled_statement"
		}
		diagnose: {
			severity: "hint"
			message:  "labeled statement"
		}
	}
	}
}
