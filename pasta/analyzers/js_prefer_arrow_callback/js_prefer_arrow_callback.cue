// js_prefer_arrow_callback flags function expression used as a callback.
// ESLint `prefer-arrow-callback` covers the same ground.

package js_prefer_arrow_callback

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

js_prefer_arrow_callback: schema.#Analyzer & {
	name:    "js_prefer_arrow_callback"
	version: "0.1.0"
	doc:     "function expression used as a callback"
	facts: {}
	rules: {
	js_prefer_arrow_callback: _base & {
		name: "js_prefer_arrow_callback"
		doc:  "function expression used as a callback"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				arguments: {
					node: "arguments"
					children: [{node: "function_expression"}]
				}
			}
		}
		diagnose: {
			severity: "hint"
			message:  "function expression used as a callback"
		}
	}
	}
}
