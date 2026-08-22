// js_func_names flags unnamed function expression.
// ESLint `func-names` covers the same ground.

package js_func_names

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

js_func_names: schema.#Analyzer & {
	name:    "js_func_names"
	version: "0.1.0"
	doc:     "unnamed function expression"
	facts: {}
	rules: {
	js_func_names: _base & {
		name: "js_func_names"
		doc:  "unnamed function expression"
		requires: []
		provides: []
		match: {
			node: "function_expression"
			absent_fields: ["name"]
		}
		diagnose: {
			severity: "hint"
			message:  "unnamed function expression"
		}
	}
	}
}
