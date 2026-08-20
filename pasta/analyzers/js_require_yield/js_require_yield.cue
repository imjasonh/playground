// js_require_yield flags generator with no yield.
// ESLint `require-yield` covers the same ground.

package js_require_yield

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

js_require_yield: schema.#Analyzer & {
	name:    "js_require_yield"
	version: "0.1.0"
	doc:     "generator with no yield"
	facts: {}
	rules: {
	js_require_yield: _base & {
		name: "js_require_yield"
		doc:  "generator with no yield"
		requires: []
		provides: []
		match: {
			node: "generator_function_declaration"
			fields: {
				body: {capture: "body", pattern: {node: "statement_block"}}
			}
			where: [{op: "subtree_lacks", args: ["@body", "yield_expression"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "generator with no yield"
		}
	}
	}
}
