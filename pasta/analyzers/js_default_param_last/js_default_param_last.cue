// js_default_param_last flags default parameter followed by a required parameter.
// ESLint `default-param-last` covers the same ground.

package js_default_param_last

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

js_default_param_last: schema.#Analyzer & {
	name:    "js_default_param_last"
	version: "0.1.0"
	doc:     "default parameter followed by a required parameter"
	facts: {}
	rules: {
	js_default_param_last: _base & {
		name: "js_default_param_last"
		doc:  "default parameter followed by a required parameter"
		requires: []
		provides: []
		match: {
			node: "formal_parameters"
			adjacent: [
				{node: "assignment_pattern"},
				{node: "identifier"},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "default parameter followed by a required parameter"
		}
	}
	}
}
