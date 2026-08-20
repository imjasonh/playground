// js_no_unsafe_finally flags control flow in a finally block.
// ESLint `no-unsafe-finally` covers the same ground.

package js_no_unsafe_finally

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

js_no_unsafe_finally: schema.#Analyzer & {
	name:    "js_no_unsafe_finally"
	version: "0.1.0"
	doc:     "control flow in a finally block"
	facts: {}
	rules: {
	js_no_unsafe_finally: _base & {
		name: "js_no_unsafe_finally"
		doc:  "control flow in a finally block"
		requires: []
		provides: []
		match: {
			node: "finally_clause"
			fields: {
				body: {capture: "body"}
			}
			where: [{op: "matches", args: ["@body", "\\b(return|throw|break|continue)\\b"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "control flow in a finally block"
		}
	}
	}
}
