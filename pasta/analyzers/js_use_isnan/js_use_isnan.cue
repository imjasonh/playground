// js_use_isnan flags compare with isNaN / Number.isNaN instead of NaN.
// ESLint `use-isnan` covers the same ground.

package js_use_isnan

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

js_use_isnan: schema.#Analyzer & {
	name:    "js_use_isnan"
	version: "0.1.0"
	doc:     "compare with isNaN / Number.isNaN instead of NaN"
	facts: {}
	rules: {
	js_use_isnan: _base & {
		name: "js_use_isnan"
		doc:  "compare with isNaN / Number.isNaN instead of NaN"
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
				{op: "matches", args: ["@op", "^(===|!==|==|!=)$"]},
				{op: "eq", args: ["@right", "NaN"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "compare with isNaN / Number.isNaN instead of NaN"
		}
	}
	js_use_isnan_left: _base & {
		name: "js_use_isnan_left"
		doc:  "compare with isNaN / Number.isNaN instead of NaN on the left"
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
				{op: "matches", args: ["@op", "^(===|!==|==|!=)$"]},
				{op: "eq", args: ["@left", "NaN"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "compare with isNaN / Number.isNaN instead of NaN on the left"
		}
	}
	}
}
