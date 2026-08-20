// js_no_empty_character_class flags empty character class in a regular expression.
// ESLint `no-empty-character-class` covers the same ground.

package js_no_empty_character_class

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

js_no_empty_character_class: schema.#Analyzer & {
	name:    "js_no_empty_character_class"
	version: "0.1.0"
	doc:     "empty character class in a regular expression"
	facts: {}
	rules: {
	js_no_empty_character_class: _base & {
		name: "js_no_empty_character_class"
		doc:  "empty character class in a regular expression"
		requires: []
		provides: []
		match: {
			node: "regex_pattern"
			where: [{op: "matches", args: ["@_root", "\\[\\]"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "empty character class in a regular expression"
		}
	}
	}
}
