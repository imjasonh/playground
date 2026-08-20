// js_no_empty_static_block flags empty class static block.
// ESLint `no-empty-static-block` covers the same ground.

package js_no_empty_static_block

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

js_no_empty_static_block: schema.#Analyzer & {
	name:    "js_no_empty_static_block"
	version: "0.1.0"
	doc:     "empty class static block"
	facts: {}
	rules: {
	js_no_empty_static_block: _base & {
		name: "js_no_empty_static_block"
		doc:  "empty class static block"
		requires: []
		provides: []
		match: {
			node: "class_static_block"
			fields: {
				body: {capture: "body", pattern: {node: "statement_block"}}
			}
			where: [{op: "empty", args: ["@body"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "empty class static block"
		}
	}
	}
}
