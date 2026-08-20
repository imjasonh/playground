// js_no_empty flags empty if block.
// ESLint `no-empty` covers the same ground.

package js_no_empty

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

js_no_empty: schema.#Analyzer & {
	name:    "js_no_empty"
	version: "0.1.0"
	doc:     "empty if block"
	facts: {}
	rules: {
	js_no_empty_if: _base & {
		name: "js_no_empty_if"
		doc:  "empty if block"
		requires: []
		provides: []
		match: {
			node: "if_statement"
			fields: {
				consequence: {capture: "body", pattern: {node: "statement_block"}}
			}
			where: [{op: "empty", args: ["@body"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "empty if block"
		}
	}
	js_no_empty_while: _base & {
		name: "js_no_empty_while"
		doc:  "empty while block"
		requires: []
		provides: []
		match: {
			node: "while_statement"
			fields: {
				body: {capture: "body", pattern: {node: "statement_block"}}
			}
			where: [{op: "empty", args: ["@body"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "empty while block"
		}
	}
	js_no_empty_for: _base & {
		name: "js_no_empty_for"
		doc:  "empty for block"
		requires: []
		provides: []
		match: {
			node: "for_statement"
			fields: {
				body: {capture: "body", pattern: {node: "statement_block"}}
			}
			where: [{op: "empty", args: ["@body"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "empty for block"
		}
	}
	}
}
