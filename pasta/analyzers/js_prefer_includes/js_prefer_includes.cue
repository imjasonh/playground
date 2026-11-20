// js_prefer_includes flags `.indexOf(...)` containment checks against
// `-1` or `0` and rewrites them to `.includes(...)` / `!.includes(...)`.
// ESLint `prefer-includes` covers the same ground.

package js_prefer_includes

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_langs: [jslang.Name, tslang.Name, tsxlang.Name]

_indexOfPattern: {
	node: "binary_expression"
	fields: {
		left: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						object:   {capture: "obj"}
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
				arguments: {capture: "args"}
			}
		}
		operator: {capture: "op"}
		right:    {capture: "rhs"}
	}
}

js_prefer_includes: schema.#Analyzer & {
	name:    "js_prefer_includes"
	version: "0.1.0"
	doc:     "Prefer .includes() over .indexOf() comparisons"
	facts: {}

	rules: {
		index_of_ne_neg_one: {
			name:      "index_of_ne_neg_one"
			doc:       "Rewrite x.indexOf(y) !== -1 / != -1 / > -1 to x.includes(y)"
			languages: _langs
			requires: []
			provides: []

			match: _indexOfPattern & {
				where: [
					{op: "eq", args: ["@prop", "indexOf"]},
					{op: "matches", args: ["@op", "^(!==|!=|>)$"]},
					{op: "matches", args: ["@rhs", "^-1$"]},
				]
			}

			diagnose: {
				message:  "use .includes() instead of comparing .indexOf()"
				severity: "warning"
			}

			rewrite: edits: [{target: "_root", replacement: "@obj.includes@args"}]
		}

		index_of_gte_zero: {
			name:      "index_of_gte_zero"
			doc:       "Rewrite x.indexOf(y) >= 0 to x.includes(y)"
			languages: _langs
			requires: []
			provides: []

			match: _indexOfPattern & {
				where: [
					{op: "eq", args: ["@prop", "indexOf"]},
					{op: "eq", args: ["@op", ">="]},
					{op: "eq", args: ["@rhs", "0"]},
				]
			}

			diagnose: {
				message:  "use .includes() instead of comparing .indexOf()"
				severity: "warning"
			}

			rewrite: edits: [{target: "_root", replacement: "@obj.includes@args"}]
		}

		index_of_eq_neg_one: {
			name:      "index_of_eq_neg_one"
			doc:       "Rewrite x.indexOf(y) === -1 / == -1 to !x.includes(y)"
			languages: _langs
			requires: []
			provides: []

			match: _indexOfPattern & {
				where: [
					{op: "eq", args: ["@prop", "indexOf"]},
					{op: "matches", args: ["@op", "^(===|==)$"]},
					{op: "matches", args: ["@rhs", "^-1$"]},
				]
			}

			diagnose: {
				message:  "use !.includes() instead of comparing .indexOf()"
				severity: "warning"
			}

			rewrite: edits: [{target: "_root", replacement: "!@obj.includes@args"}]
		}

		index_of_lt_zero: {
			name:      "index_of_lt_zero"
			doc:       "Rewrite x.indexOf(y) < 0 to !x.includes(y)"
			languages: _langs
			requires: []
			provides: []

			match: _indexOfPattern & {
				where: [
					{op: "eq", args: ["@prop", "indexOf"]},
					{op: "eq", args: ["@op", "<"]},
					{op: "eq", args: ["@rhs", "0"]},
				]
			}

			diagnose: {
				message:  "use !.includes() instead of comparing .indexOf()"
				severity: "warning"
			}

			rewrite: edits: [{target: "_root", replacement: "!@obj.includes@args"}]
		}
	}
}
