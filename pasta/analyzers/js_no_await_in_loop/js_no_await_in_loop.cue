// js_no_await_in_loop flags await inside a loop.
// ESLint `no-await-in-loop` covers the same ground.

package js_no_await_in_loop

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

js_no_await_in_loop: schema.#Analyzer & {
	name:    "js_no_await_in_loop"
	version: "0.1.0"
	doc:     "await inside a loop"
	facts: {}
	rules: {
	js_no_await_in_loop: _base & {
		name: "js_no_await_in_loop"
		doc:  "await inside a loop"
		requires: []
		provides: []
		match: {
			node: "await_expression"
			where: [{
				op: "ancestor_is"
				args: ["@_root", ["for_statement", "for_in_statement", "while_statement", "do_statement"]]
			}]
		}
		diagnose: {
			severity: "warning"
			message:  "await inside a loop"
		}
	}
	}
}
