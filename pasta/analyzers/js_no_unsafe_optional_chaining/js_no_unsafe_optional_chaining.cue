// js_no_unsafe_optional_chaining flags optional chain used as a call callee inside parentheses.
// ESLint `no-unsafe-optional-chaining` covers the same ground.

package js_no_unsafe_optional_chaining

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

js_no_unsafe_optional_chaining: schema.#Analyzer & {
	name:    "js_no_unsafe_optional_chaining"
	version: "0.1.0"
	doc:     "optional chain used as a call callee inside parentheses"
	facts: {}
	rules: {
	js_no_unsafe_optional_chaining_call: _base & {
		name: "js_no_unsafe_optional_chaining_call"
		doc:  "optional chain used as a call callee inside parentheses"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "parenthesized_expression"
					children: [{capture: "inner"}]
				}
			}
			where: [{op: "matches", args: ["@inner", "\\?\\."]}]
		}
		diagnose: {
			severity: "warning"
			message:  "optional chain used as a call callee inside parentheses"
		}
	}
	js_no_unsafe_optional_chaining_member: _base & {
		name: "js_no_unsafe_optional_chaining_member"
		doc:  "optional chain used as a member object inside parentheses"
		requires: []
		provides: []
		match: {
			node: "member_expression"
			fields: {
				object: {
					node: "parenthesized_expression"
					children: [{capture: "inner"}]
				}
			}
			where: [{op: "matches", args: ["@inner", "\\?\\."]}]
		}
		diagnose: {
			severity: "warning"
			message:  "optional chain used as a member object inside parentheses"
		}
	}
	js_no_unsafe_optional_chaining_new: _base & {
		name: "js_no_unsafe_optional_chaining_new"
		doc:  "optional chain used as a new constructor"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor"}
			}
			where: [{op: "matches", args: ["@ctor", "\\?\\."]}]
		}
		diagnose: {
			severity: "warning"
			message:  "optional chain used as a new constructor"
		}
	}
	}
}
