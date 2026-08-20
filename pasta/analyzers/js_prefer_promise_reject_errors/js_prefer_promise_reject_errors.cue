// js_prefer_promise_reject_errors flags Promise.reject with a non-Error.
// ESLint `prefer-promise-reject-errors` covers the same ground.

package js_prefer_promise_reject_errors

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

js_prefer_promise_reject_errors: schema.#Analyzer & {
	name:    "js_prefer_promise_reject_errors"
	version: "0.1.0"
	doc:     "Promise.reject with a non-Error"
	facts: {}
	rules: {
	js_prefer_promise_reject_errors: _base & {
		name: "js_prefer_promise_reject_errors"
		doc:  "Promise.reject with a non-Error"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						object: {capture: "obj", pattern: {node: "identifier"}}
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
				arguments: {
					node: "arguments"
					children: [{capture: "reason", pattern: {node: ["string", "number", "true", "false", "null", "undefined"]}}]
				}
			}
			where: [
				{op: "eq", args: ["@obj", "Promise"]},
				{op: "eq", args: ["@prop", "reject"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "Promise.reject with a non-Error"
		}
	}
	}
}
