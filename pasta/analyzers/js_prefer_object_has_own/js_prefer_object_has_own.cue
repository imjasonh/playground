// js_prefer_object_has_own flags Object.prototype.hasOwnProperty.call instead of Object.hasOwn.
// ESLint `prefer-object-has-own` covers the same ground.

package js_prefer_object_has_own

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

js_prefer_object_has_own: schema.#Analyzer & {
	name:    "js_prefer_object_has_own"
	version: "0.1.0"
	doc:     "Object.prototype.hasOwnProperty.call instead of Object.hasOwn"
	facts: {}
	rules: {
	js_prefer_object_has_own: _base & {
		name: "js_prefer_object_has_own"
		doc:  "Object.prototype.hasOwnProperty.call instead of Object.hasOwn"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn"}
			}
			where: [{op: "matches", args: ["@fn", "Object\\.prototype\\.hasOwnProperty\\.call"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "Object.prototype.hasOwnProperty.call instead of Object.hasOwn"
		}
	}
	}
}
