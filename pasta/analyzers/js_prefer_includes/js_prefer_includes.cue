// js_prefer_includes flags `.indexOf(...)` comparisons against `-1` or `0`
// that can be written more clearly with `.includes(...)`.
// ESLint `prefer-includes` covers the same ground.

package js_prefer_includes

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_langs: [jslang.Name, tslang.Name, tsxlang.Name]

js_prefer_includes: schema.#Analyzer & {
	name:    "js_prefer_includes"
	version: "0.1.0"
	doc:     "Prefer .includes() over .indexOf() comparisons"
	facts: {}

	rules: index_of_comparison: {
		name:      "index_of_comparison"
		doc:       "Flag indexOf comparisons to -1 or >= 0"
		languages: _langs
		requires: []
		provides: []

		match: {
			node: "binary_expression"
			fields: {
				left: {
					node: "call_expression"
					fields: {
						function: {
							node: "member_expression"
							fields: {
								property: {capture: "prop", pattern: {node: "property_identifier"}}
							}
						}
					}
				}
				operator: {capture: "op"}
				right:    {capture: "rhs"}
			}
			where: [
				{op: "eq", args: ["@prop", "indexOf"]},
				{op: "matches", args: ["@op", "^(===|!==|==|!=|>=|<|>)$"]},
				{op: "matches", args: ["@rhs", "^(-1|0)$"]},
			]
		}

		diagnose: {
			message:  "use .includes() instead of comparing .indexOf()"
			severity: "hint"
		}
	}
}
