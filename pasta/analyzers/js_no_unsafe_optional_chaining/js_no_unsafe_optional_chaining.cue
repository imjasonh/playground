// js_no_unsafe_optional_chaining flags `(obj?.foo)()` / `(obj?.foo).bar`
// / `new (obj?.Foo)` — parentheses around an optional chain force a
// throw when the chain is undefined. ESLint `no-unsafe-optional-chaining`
// covers the same ground.
//
// The inner node must itself be a member, subscript, or call. A
// coalescing fallback (`(obj?.foo ?? bar).trim()`) is a binary
// expression inside the parens and is left alone.

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

_parenOptional: {
	node: "parenthesized_expression"
	children: [{
		capture: "inner"
		pattern: {
			node: ["member_expression", "subscript_expression", "call_expression"]
			where: [{op: "matches", args: ["@_root", "\\?\\."]}]
		}
	}]
}

js_no_unsafe_optional_chaining: schema.#Analyzer & {
	name:    "js_no_unsafe_optional_chaining"
	version: "0.1.0"
	doc:     "optional chain used as a call callee, member object, or constructor inside parentheses"
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
					function: _parenOptional
				}
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
					object: _parenOptional
				}
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
					constructor: _parenOptional
				}
			}
			diagnose: {
				severity: "warning"
				message:  "optional chain used as a new constructor"
			}
		}
	}
}
