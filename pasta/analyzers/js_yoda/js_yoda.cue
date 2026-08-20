// js_yoda flags literal on the left of a comparison.
// ESLint `yoda` covers the same ground.

package js_yoda

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

js_yoda: schema.#Analyzer & {
	name:    "js_yoda"
	version: "0.1.0"
	doc:     "literal on the left of a comparison"
	facts: {}
	rules: {
	js_yoda: _base & {
		name: "js_yoda"
		doc:  "literal on the left of a comparison"
		requires: []
		provides: []
		match: {
			node: "binary_expression"
			fields: {
				left: {capture: "left"}
				operator: {capture: "op"}
				right: {capture: "right", pattern: {node: "identifier"}}
			}
			where: [
				{op: "matches", args: ["@op", "^(===|!==|==|!=|<|<=|>|>=)$"]},
				{op: "node_is", args: ["@left", ["number", "string", "true", "false", "null"]]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "literal on the left of a comparison"
		}
	}
	}
}
