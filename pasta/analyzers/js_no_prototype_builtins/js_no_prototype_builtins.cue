// js_no_prototype_builtins flags do not call Object.prototype methods directly on the object.
// ESLint `no-prototype-builtins` covers the same ground.

package js_no_prototype_builtins

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

js_no_prototype_builtins: schema.#Analyzer & {
	name:    "js_no_prototype_builtins"
	version: "0.1.0"
	doc:     "do not call Object.prototype methods directly on the object"
	facts: {}
	rules: {
	js_no_prototype_builtins: _base & {
		name: "js_no_prototype_builtins"
		doc:  "do not call Object.prototype methods directly on the object"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
			}
			where: [{op: "matches", args: ["@prop", "^(hasOwnProperty|isPrototypeOf|propertyIsEnumerable)$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "do not call Object.prototype methods directly on the object"
		}
	}
	}
}
