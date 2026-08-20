// js_no_unsafe_negation flags negating the left operand of in / instanceof.
// ESLint `no-unsafe-negation` covers the same ground.

package js_no_unsafe_negation

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

js_no_unsafe_negation: schema.#Analyzer & {
	name:    "js_no_unsafe_negation"
	version: "0.1.0"
	doc:     "negating the left operand of in / instanceof"
	facts: {}
	rules: {
	js_no_unsafe_negation: _base & {
		name: "js_no_unsafe_negation"
		doc:  "negating the left operand of in / instanceof"
		requires: []
		provides: []
		match: {
			node: "binary_expression"
			fields: {
				left: {capture: "left", pattern: {node: "unary_expression"}}
				operator: {capture: "op"}
				right: {capture: "right"}
			}
			where: [
				{op: "matches", args: ["@op", "^(in|instanceof)$"]},
				{op: "matches", args: ["@left", "^!"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "negating the left operand of in / instanceof"
		}
	}
	}
}
