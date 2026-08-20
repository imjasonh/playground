// js_no_new_native_nonconstructor flags new on a value that is not a constructor.
// ESLint `no-new-native-nonconstructor` covers the same ground.

package js_no_new_native_nonconstructor

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

js_no_new_native_nonconstructor: schema.#Analyzer & {
	name:    "js_no_new_native_nonconstructor"
	version: "0.1.0"
	doc:     "new on a value that is not a constructor"
	facts: {}
	rules: {
	js_no_new_native_nonconstructor: _base & {
		name: "js_no_new_native_nonconstructor"
		doc:  "new on a value that is not a constructor"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor", pattern: {node: "identifier"}}
			}
			where: [{op: "matches", args: ["@ctor", "^(Symbol|BigInt|Math|JSON|Reflect|Intl|Atomics)$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "new on a value that is not a constructor"
		}
	}
	}
}
