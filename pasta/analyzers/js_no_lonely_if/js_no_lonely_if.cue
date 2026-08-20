// js_no_lonely_if flags if as the only statement in an else block.
// ESLint `no-lonely-if` covers the same ground.

package js_no_lonely_if

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

js_no_lonely_if: schema.#Analyzer & {
	name:    "js_no_lonely_if"
	version: "0.1.0"
	doc:     "if as the only statement in an else block"
	facts: {}
	rules: {
	js_no_lonely_if: _base & {
		name: "js_no_lonely_if"
		doc:  "if as the only statement in an else block"
		requires: []
		provides: []
		match: {
			node: "else_clause"
			children: [{
				capture: "body"
				pattern: {
					node: "statement_block"
					children: [{node: "if_statement"}]
				}
			}]
			where: [{op: "named_child_count", args: ["@body", "1"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "if as the only statement in an else block"
		}
	}
	}
}
