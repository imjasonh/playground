// js_no_useless_call flags .call/.apply with null or undefined this.
// ESLint `no-useless-call` covers the same ground.

package js_no_useless_call

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

js_no_useless_call: schema.#Analyzer & {
	name:    "js_no_useless_call"
	version: "0.1.0"
	doc:     ".call/.apply with null or undefined this"
	facts: {}
	rules: {
	js_no_useless_call: _base & {
		name: "js_no_useless_call"
		doc:  ".call/.apply with null or undefined this"
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
				arguments: {
					node: "arguments"
					children: [{capture: "thisarg", pattern: {node: ["null", "undefined"]}}]
				}
			}
			where: [{op: "matches", args: ["@prop", "^(call|apply)$"]}]
		}
		diagnose: {
			severity: "hint"
			message:  ".call/.apply with null or undefined this"
		}
	}
	}
}
