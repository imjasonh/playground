// js_arrow_body_style flags arrow function block that only returns.
// ESLint `arrow-body-style` covers the same ground.

package js_arrow_body_style

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

js_arrow_body_style: schema.#Analyzer & {
	name:    "js_arrow_body_style"
	version: "0.1.0"
	doc:     "arrow function block that only returns"
	facts: {}
	rules: {
	js_arrow_body_style: _base & {
		name: "js_arrow_body_style"
		doc:  "arrow function block that only returns"
		requires: []
		provides: []
		match: {
			node: "arrow_function"
			fields: {
				body: {
					capture: "body"
					pattern: {
						node: "statement_block"
						children: [{
							node: "return_statement"
							children: [{capture: "val"}]
						}]
					}
				}
			}
			where: [{op: "named_child_count", args: ["@body", "1"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "arrow function block that only returns"
		}
	}
	}
}
