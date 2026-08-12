// rust_unwrap flags `.unwrap()` / `.expect(...)` calls. Both panic on
// Err/None — fine in prototypes and tests, rarely what you want in
// library or production code. Prefer `?`, `unwrap_or`, or an explicit
// match. No auto-fix (the right recovery is per-call-site).

package rust_unwrap

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

rust_unwrap: schema.#Analyzer & {
	name:    "rust_unwrap"
	version: "0.1.0"
	doc:     "Flag .unwrap() / .expect() that panic on failure"
	facts: {}

	rules: unwrap_call: {
		name:      "unwrap_call"
		doc:       "Flag .unwrap() / .expect(...)"
		languages: [rustlang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "field_expression"
					fields: {
						field: {capture: "method", pattern: {node: "field_identifier"}}
					}
				}
			}
			where: [{op: "matches", args: ["@method", "^(unwrap|expect)$"]}]
		}

		diagnose: {
			severity: "warning"
			message:  ".unwrap()/.expect() panics on failure; prefer ? or an explicit match"
		}
	}
}
