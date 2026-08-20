// js_no_empty_pattern flags empty destructuring pattern.
// ESLint `no-empty-pattern` covers the same ground.

package js_no_empty_pattern

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

js_no_empty_pattern: schema.#Analyzer & {
	name:    "js_no_empty_pattern"
	version: "0.1.0"
	doc:     "empty destructuring pattern"
	facts: {}
	rules: {
	js_no_empty_pattern: _base & {
		name: "js_no_empty_pattern"
		doc:  "empty destructuring pattern"
		requires: []
		provides: []
		match: {
			node: ["array_pattern", "object_pattern"]
			where: [{op: "empty", args: ["@_root"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "empty destructuring pattern"
		}
	}
	}
}
