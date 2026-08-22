// js_prefer_named_capture_group flags unnamed capturing group in a regular expression.
// ESLint `prefer-named-capture-group` covers the same ground.

package js_prefer_named_capture_group

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

js_prefer_named_capture_group: schema.#Analyzer & {
	name:    "js_prefer_named_capture_group"
	version: "0.1.0"
	doc:     "unnamed capturing group in a regular expression"
	facts: {}
	rules: {
	js_prefer_named_capture_group: _base & {
		name: "js_prefer_named_capture_group"
		doc:  "unnamed capturing group in a regular expression"
		requires: []
		provides: []
		match: {
			node: "regex_pattern"
			where: [
				{op: "matches", args: ["@_root", "\\([^?]"]},
				{op: "not_matches", args: ["@_root", "\\(\\?"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "unnamed capturing group in a regular expression"
		}
	}
	}
}
