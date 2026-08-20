// js_preserve_caught_error flags `catch (e) { throw new Error(...) }`
// when the thrown `new` expression does not pass `{ cause: … }`.
// ESLint `preserve-caught-error` covers the same ground. The word
// "because" in a message is not treated as a cause property.

package js_preserve_caught_error

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

js_preserve_caught_error: schema.#Analyzer & {
	name:    "js_preserve_caught_error"
	version: "0.1.0"
	doc:     "throwing a new error from catch without passing the cause"
	facts: {}
	rules: {
	js_preserve_caught_error: _base & {
		name: "js_preserve_caught_error"
		doc:  "throwing a new error from catch without passing the cause"
		requires: []
		provides: []
		match: {
			node: "catch_clause"
			fields: {
				parameter: {capture: "param", pattern: {node: "identifier"}}
				body: {
					node: "statement_block"
					children: [{
						node: "throw_statement"
						children: [{
							capture: "thrown"
							pattern: {node: "new_expression"}
						}]
					}]
				}
			}
			where: [{op: "not_matches", args: ["@thrown", "\\bcause\\s*:"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "throwing a new error from catch without passing the cause"
		}
	}
	}
}
