// js_no_unreachable flags statement after return/throw/break/continue.
// ESLint `no-unreachable` covers the same ground.

package js_no_unreachable

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

js_no_unreachable: schema.#Analyzer & {
	name:    "js_no_unreachable"
	version: "0.1.0"
	doc:     "statement after return/throw/break/continue"
	facts: {}
	rules: {
	js_no_unreachable: _base & {
		name: "js_no_unreachable"
		doc:  "statement after return/throw/break/continue"
		requires: []
		provides: []
		match: {
			node: "statement_block"
			adjacent: [
				{capture: "term", pattern: {node: ["return_statement", "throw_statement", "break_statement", "continue_statement"]}},
				{capture: "dead", pattern: {node: ["expression_statement", "return_statement", "if_statement", "for_statement", "for_in_statement", "while_statement", "do_statement", "lexical_declaration", "variable_declaration", "throw_statement", "try_statement", "switch_statement"]}},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "statement after return/throw/break/continue"
		}
	}
	}
}
