// js_no_sequences flags comma (sequence) expression.
// ESLint `no-sequences` covers the same ground.

package js_no_sequences

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

js_no_sequences: schema.#Analyzer & {
	name:    "js_no_sequences"
	version: "0.1.0"
	doc:     "comma (sequence) expression"
	facts: {}
	rules: {
	js_no_sequences: _base & {
		name: "js_no_sequences"
		doc:  "comma (sequence) expression"
		requires: []
		provides: []
		match: {
			node: "sequence_expression"
		}
		diagnose: {
			severity: "hint"
			message:  "comma (sequence) expression"
		}
	}
	}
}
