// js_no_eq_null flags == null / != null.
// ESLint `no-eq-null` covers the same ground.

package js_no_eq_null

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

js_no_eq_null: schema.#Analyzer & {
	name:    "js_no_eq_null"
	version: "0.1.0"
	doc:     "== null / != null"
	facts: {}
	rules: {
	js_no_eq_null: _base & {
		name: "js_no_eq_null"
		doc:  "== null / != null"
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
				{op: "matches", args: ["@op", "^(==|!=)$"]},
				{op: "eq", args: ["@right", "null"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "== null / != null"
		}
	}
	}
}
