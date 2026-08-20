// js_prefer_rest_params flags arguments identifier; prefer rest parameters.
// ESLint `prefer-rest-params` covers the same ground.

package js_prefer_rest_params

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

js_prefer_rest_params: schema.#Analyzer & {
	name:    "js_prefer_rest_params"
	version: "0.1.0"
	doc:     "arguments identifier; prefer rest parameters"
	facts: {}
	rules: {
	js_prefer_rest_params: _base & {
		name: "js_prefer_rest_params"
		doc:  "arguments identifier; prefer rest parameters"
		requires: []
		provides: []
		match: {
			node: "identifier"
			where: [{op: "eq", args: ["@_root", "arguments"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "arguments identifier; prefer rest parameters"
		}
	}
	}
}
