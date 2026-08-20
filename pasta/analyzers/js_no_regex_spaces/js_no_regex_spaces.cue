// js_no_regex_spaces flags multiple consecutive spaces in a regular expression.
// ESLint `no-regex-spaces` covers the same ground.

package js_no_regex_spaces

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

js_no_regex_spaces: schema.#Analyzer & {
	name:    "js_no_regex_spaces"
	version: "0.1.0"
	doc:     "multiple consecutive spaces in a regular expression"
	facts: {}
	rules: {
	js_no_regex_spaces: _base & {
		name: "js_no_regex_spaces"
		doc:  "multiple consecutive spaces in a regular expression"
		requires: []
		provides: []
		match: {
			node: "regex_pattern"
			where: [{op: "matches", args: ["@_root", "  "]}]
		}
		diagnose: {
			severity: "warning"
			message:  "multiple consecutive spaces in a regular expression"
		}
	}
	}
}
