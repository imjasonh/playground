// js_default_case_last flags default clause is not last.
// ESLint `default-case-last` covers the same ground.

package js_default_case_last

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

js_default_case_last: schema.#Analyzer & {
	name:    "js_default_case_last"
	version: "0.1.0"
	doc:     "default clause is not last"
	facts: {}
	rules: {
	js_default_case_last: _base & {
		name: "js_default_case_last"
		doc:  "default clause is not last"
		requires: []
		provides: []
		match: {
			node: "switch_body"
			adjacent: [
				{node: "switch_default"},
				{node: "switch_case"},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "default clause is not last"
		}
	}
	}
}
