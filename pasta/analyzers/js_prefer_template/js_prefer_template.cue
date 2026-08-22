// js_prefer_template flags string concatenation with +.
// ESLint `prefer-template` covers the same ground.

package js_prefer_template

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

js_prefer_template: schema.#Analyzer & {
	name:    "js_prefer_template"
	version: "0.1.0"
	doc:     "string concatenation with +"
	facts: {}
	rules: {
	js_prefer_template: _base & {
		name: "js_prefer_template"
		doc:  "string concatenation with +"
		requires: []
		provides: []
		match: {
			node: "binary_expression"
			fields: {
				left: {capture: "left"}
				operator: {capture: "op"}
				right: {capture: "right"}
			}
			where: [
				{op: "token_eq", args: ["@op", "+"]},
				{op: "node_is", args: ["@left", "string"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "string concatenation with +"
		}
	}
	}
}
