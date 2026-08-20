// js_no_setter_return flags a setter that returns a value. A setter's
// return is ignored by the language; returning a value is almost
// always leftover from a getter or a fluent method. ESLint
// `no-setter-return` covers the same ground.
//
// The match requires the method to *start* with `set ` (optional
// `static` / `async`) so a method that declares `const set = …` and
// later `return set` is not treated as a setter. Bare `return;` is
// allowed.

package js_no_setter_return

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

js_no_setter_return: schema.#Analyzer & {
	name:    "js_no_setter_return"
	version: "0.1.0"
	doc:     "setter returns a value"
	facts: {}
	rules: {
		js_no_setter_return: _base & {
			name: "js_no_setter_return"
			doc:  "setter returns a value"
			requires: []
			provides: []
			match: {
				node: "method_definition"
				fields: {
					body: {capture: "body"}
				}
				where: [
					{op: "matches", args: ["@_root", "^(static\\s+)?(async\\s+)?set\\s"]},
					{op: "matches", args: ["@body", "\\breturn\\s+[^;\\s]"]},
				]
			}
			diagnose: {
				severity: "warning"
				message:  "setter returns a value"
			}
		}
	}
}
