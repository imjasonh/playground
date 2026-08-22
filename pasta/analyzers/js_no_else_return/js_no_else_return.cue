// js_no_else_return flags else after a returning if.
// ESLint `no-else-return` covers the same ground.

package js_no_else_return

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

js_no_else_return: schema.#Analyzer & {
	name:    "js_no_else_return"
	version: "0.1.0"
	doc:     "else after a returning if"
	facts: {}
	rules: {
	js_no_else_return: _base & {
		name: "js_no_else_return"
		doc:  "else after a returning if"
		requires: []
		provides: []
		match: {
			node: "if_statement"
			fields: {
				consequence: {
					capture: "cons"
					pattern: {
						node: ["return_statement", "statement_block"]
					}
				}
				alternative: {capture: "alt", pattern: {node: "else_clause"}}
			}
			where: [{op: "matches", args: ["@cons", "\\breturn\\b"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "else after a returning if"
		}
	}
	}
}
