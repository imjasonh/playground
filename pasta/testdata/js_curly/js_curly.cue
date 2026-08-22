// js_curly flags if-statement consequence is not a block.
// ESLint `curly` covers the same ground.

package js_curly

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

js_curly: schema.#Analyzer & {
	name:    "js_curly"
	version: "0.1.0"
	doc:     "if-statement consequence is not a block"
	facts: {}
	rules: {
	js_curly: _base & {
		name: "js_curly"
		doc:  "if-statement consequence is not a block"
		requires: []
		provides: []
		match: {
			node: "if_statement"
			fields: {
				consequence: {capture: "cons"}
			}
			where: [{op: "node_is_not", args: ["@cons", "statement_block"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "if-statement consequence is not a block"
		}
	}
	}
}
