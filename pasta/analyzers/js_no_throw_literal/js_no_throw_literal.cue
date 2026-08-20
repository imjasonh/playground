// js_no_throw_literal flags throw of a literal.
// ESLint `no-throw-literal` covers the same ground.

package js_no_throw_literal

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

js_no_throw_literal: schema.#Analyzer & {
	name:    "js_no_throw_literal"
	version: "0.1.0"
	doc:     "throw of a literal"
	facts: {}
	rules: {
	js_no_throw_literal: _base & {
		name: "js_no_throw_literal"
		doc:  "throw of a literal"
		requires: []
		provides: []
		match: {
			node: "throw_statement"
			children: [{capture: "val", pattern: {node: ["string", "number", "true", "false", "null", "undefined", "object", "array"]}}]
		}
		diagnose: {
			severity: "hint"
			message:  "throw of a literal"
		}
	}
	}
}
