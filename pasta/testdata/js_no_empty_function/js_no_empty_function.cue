// js_no_empty_function flags empty function body.
// ESLint `no-empty-function` covers the same ground.

package js_no_empty_function

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

js_no_empty_function: schema.#Analyzer & {
	name:    "js_no_empty_function"
	version: "0.1.0"
	doc:     "empty function body"
	facts: {}
	rules: {
	js_no_empty_function: _base & {
		name: "js_no_empty_function"
		doc:  "empty function body"
		requires: []
		provides: []
		match: {
			node: ["function_declaration", "function_expression", "arrow_function", "method_definition", "generator_function_declaration"]
			fields: {
				body: {capture: "body", pattern: {node: "statement_block"}}
			}
			where: [{op: "empty", args: ["@body"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "empty function body"
		}
	}
	}
}
