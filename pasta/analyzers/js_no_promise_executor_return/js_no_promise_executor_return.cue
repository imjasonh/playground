// js_no_promise_executor_return flags returning a value from a Promise executor.
// ESLint `no-promise-executor-return` covers the same ground.

package js_no_promise_executor_return

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

js_no_promise_executor_return: schema.#Analyzer & {
	name:    "js_no_promise_executor_return"
	version: "0.1.0"
	doc:     "returning a value from a Promise executor"
	facts: {}
	rules: {
	js_no_promise_executor_return: _base & {
		name: "js_no_promise_executor_return"
		doc:  "returning a value from a Promise executor"
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
				{op: "matches", args: ["@exec", "\\breturn\\s+\\S"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "returning a value from a Promise executor"
		}
	}
	}
}
