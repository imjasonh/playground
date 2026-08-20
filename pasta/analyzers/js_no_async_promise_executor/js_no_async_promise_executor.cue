// js_no_async_promise_executor flags Promise executor must not be async.
// ESLint `no-async-promise-executor` covers the same ground.

package js_no_async_promise_executor

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

js_no_async_promise_executor: schema.#Analyzer & {
	name:    "js_no_async_promise_executor"
	version: "0.1.0"
	doc:     "Promise executor must not be async"
	facts: {}
	rules: {
	js_no_async_promise_executor: _base & {
		name: "js_no_async_promise_executor"
		doc:  "Promise executor must not be async"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor", pattern: {node: "identifier"}}
				arguments: {
					node: "arguments"
					children: [{capture: "exec"}]
				}
			}
			where: [
				{op: "eq", args: ["@ctor", "Promise"]},
				{op: "matches", args: ["@exec", "^async\\b"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "Promise executor must not be async"
		}
	}
	}
}
