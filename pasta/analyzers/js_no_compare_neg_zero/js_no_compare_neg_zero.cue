// js_no_compare_neg_zero flags do not compare against -0.
// ESLint `no-compare-neg-zero` covers the same ground.

package js_no_compare_neg_zero

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

js_no_compare_neg_zero: schema.#Analyzer & {
	name:    "js_no_compare_neg_zero"
	version: "0.1.0"
	doc:     "do not compare against -0"
	facts: {}
	rules: {
	js_no_compare_neg_zero: _base & {
		name: "js_no_compare_neg_zero"
		doc:  "do not compare against -0"
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
				{op: "matches", args: ["@op", "^(===|!==|==|!=|<|<=|>|>=)$"]},
				{op: "matches", args: ["@right", "^-0$"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "do not compare against -0"
		}
	}
	js_no_compare_neg_zero_left: _base & {
		name: "js_no_compare_neg_zero_left"
		doc:  "do not compare against -0 on the left"
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
				{op: "matches", args: ["@op", "^(===|!==|==|!=|<|<=|>|>=)$"]},
				{op: "matches", args: ["@left", "^-0$"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "do not compare against -0 on the left"
		}
	}
	}
}
