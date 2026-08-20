// js_no_template_curly_in_string flags template placeholder syntax in a regular string.
// ESLint `no-template-curly-in-string` covers the same ground.

package js_no_template_curly_in_string

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

js_no_template_curly_in_string: schema.#Analyzer & {
	name:    "js_no_template_curly_in_string"
	version: "0.1.0"
	doc:     "template placeholder syntax in a regular string"
	facts: {}
	rules: {
	js_no_template_curly_in_string: _base & {
		name: "js_no_template_curly_in_string"
		doc:  "template placeholder syntax in a regular string"
		requires: []
		provides: []
		match: {
			node: "string"
			where: [{op: "matches", args: ["@_root", "\\$\\{"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "template placeholder syntax in a regular string"
		}
	}
	}
}
