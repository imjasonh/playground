// rust_bool_comparison flags comparisons against boolean literals
// (`x == true`, `x == false`, `true == x`, `false == x`).
// Clippy `bool_comparison` covers the same ground.

package rust_bool_comparison

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

rust_bool_comparison: schema.#Analyzer & {
	name:    "rust_bool_comparison"
	version: "0.1.0"
	doc:     "Flag comparisons to boolean literals (x == true, x == false)"
	facts: {}

	rules: {
		rhs_bool: {
			name:      "rhs_bool"
			doc:       "Flag x == true / x == false"
			languages: [rustlang.Name]
			requires: []
			provides: []

			match: {
				node: "binary_expression"
				fields: {
					operator: {capture: "op"}
					right:    {capture: "lit", pattern: {node: "boolean_literal"}}
				}
				where: [
					{op: "matches", args: ["@op", "^(==|!=)$"]},
				]
			}

			diagnose: {
				message:  "redundant comparison to boolean literal; simplify condition"
				severity: "warning"
			}
		}

		lhs_bool: {
			name:      "lhs_bool"
			doc:       "Flag true == x / false == x"
			languages: [rustlang.Name]
			requires: []
			provides: []

			match: {
				node: "binary_expression"
				fields: {
					left:     {capture: "lit", pattern: {node: "boolean_literal"}}
					operator: {capture: "op"}
				}
				where: [
					{op: "matches", args: ["@op", "^(==|!=)$"]},
				]
			}

			diagnose: {
				message:  "redundant comparison to boolean literal; simplify condition"
				severity: "warning"
			}
		}
	}
}
