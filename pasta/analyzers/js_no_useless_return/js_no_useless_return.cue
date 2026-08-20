// js_no_useless_return flags empty return as the last statement after another statement.
// ESLint `no-useless-return` covers the same ground.

package js_no_useless_return

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

js_no_useless_return: schema.#Analyzer & {
	name:    "js_no_useless_return"
	version: "0.1.0"
	doc:     "empty return as the last statement after another statement"
	facts: {}
	rules: {
	js_no_useless_return: _base & {
		name: "js_no_useless_return"
		doc:  "empty return as the last statement after another statement"
		requires: []
		provides: []
		match: {
			node: "statement_block"
			adjacent: [
				{node: ["expression_statement", "if_statement", "lexical_declaration"]},
				{
					capture: "ret"
					pattern: {node: "return_statement"}
				},
			]
			where: [{op: "named_child_count", args: ["@ret", "0"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "empty return as the last statement after another statement"
		}
	}
	}
}
