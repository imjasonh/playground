// js_require_await flags async function with no await.
// ESLint `require-await` covers the same ground.

package js_require_await

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

js_require_await: schema.#Analyzer & {
	name:    "js_require_await"
	version: "0.1.0"
	doc:     "async function with no await"
	facts: {}
	rules: {
	js_require_await: _base & {
		name: "js_require_await"
		doc:  "async function with no await"
		requires: []
		provides: []
		match: {
			node: ["function_declaration", "function_expression", "arrow_function", "method_definition"]
			fields: {
				body: {capture: "body", pattern: {node: "statement_block"}}
			}
			where: [
				{op: "matches", args: ["@_root", "^async\\b"]},
				{op: "subtree_lacks", args: ["@body", "await_expression"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "async function with no await"
		}
	}
	}
}
