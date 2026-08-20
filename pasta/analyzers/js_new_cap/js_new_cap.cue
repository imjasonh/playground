// js_new_cap flags new with a lowercase constructor.
// ESLint `new-cap` covers the same ground.

package js_new_cap

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

js_new_cap: schema.#Analyzer & {
	name:    "js_new_cap"
	version: "0.1.0"
	doc:     "new with a lowercase constructor"
	facts: {}
	rules: {
	js_new_cap: _base & {
		name: "js_new_cap"
		doc:  "new with a lowercase constructor"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor", pattern: {node: "identifier"}}
			}
			where: [{op: "matches", args: ["@ctor", "^[a-z]"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "new with a lowercase constructor"
		}
	}
	}
}
