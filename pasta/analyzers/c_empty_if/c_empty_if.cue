// c_empty_if flags `if (cond);` — an if whose then-clause is a null
// statement. The semicolon is almost always a typo (the next line was
// meant to be the body). clang-tidy flags empty if bodies; this is the
// structural form. Empty `{ }` blocks are left alone — those can be
// intentional placeholders. Applies to C and C++.

package c_empty_if

import (
	"github.com/imjasonh/pasta/schema"
	clang "github.com/imjasonh/pasta/lang/c"
	cpplang "github.com/imjasonh/pasta/lang/cpp"
)

c_empty_if: schema.#Analyzer & {
	name:    "c_empty_if"
	version: "0.1.0"
	doc:     "Flag if (cond); with an empty then-clause"
	facts: {}

	rules: empty_then: {
		name: "empty_then"
		doc:  "if (x); is almost always a typo"
		languages: [clang.Name, cpplang.Name]
		requires: []
		provides: []

		match: {
			node: "if_statement"
			fields: {
				consequence: {
					capture: "then"
					pattern: {node: "expression_statement"}
				}
			}
			where: [{op: "empty", args: ["@then"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "if has an empty then-clause (`if (cond);`); the semicolon is probably a typo"
		}
	}
}
