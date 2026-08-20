// js_no_caller flags arguments.callee or arguments.caller.
// ESLint `no-caller` covers the same ground.

package js_no_caller

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

js_no_caller: schema.#Analyzer & {
	name:    "js_no_caller"
	version: "0.1.0"
	doc:     "arguments.callee or arguments.caller"
	facts: {}
	rules: {
	js_no_caller: _base & {
		name: "js_no_caller"
		doc:  "arguments.callee or arguments.caller"
		requires: []
		provides: []
		match: {
			node: "member_expression"
			fields: {
				object: {capture: "obj", pattern: {node: "identifier"}}
				property: {capture: "prop", pattern: {node: "property_identifier"}}
			}
			where: [
				{op: "eq", args: ["@obj", "arguments"]},
				{op: "matches", args: ["@prop", "^(callee|caller)$"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "arguments.callee or arguments.caller"
		}
	}
	}
}
