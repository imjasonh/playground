// rust_catch_unwind flags panic::catch_unwind.
//
// Google Rust style prohibits catch_unwind in first-party code. It only
// works when the binary is built with panic=unwind. A defense-in-depth
// wrapper at a process entry point is the guide's exception; mark that
// call pasta:ignore rust_catch_unwind.
// https://google.github.io/styleguide/rustguide.html#catch-unwind

package rust_catch_unwind

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

rust_catch_unwind: schema.#Analyzer & {
	name:    "rust_catch_unwind"
	version: "0.1.0"
	doc:     "Flag panic::catch_unwind"
	facts: {}

	rules: rust_catch_unwind: {
		name:      "rust_catch_unwind"
		doc:       "call to catch_unwind"
		languages: [rustlang.Name]
		requires: []
		provides: []

		require_substring: ["catch_unwind"]

		match: {
			node: "call_expression"
			fields: function: {capture: "fn"}
			where: [{op: "matches", args: ["@fn", "(^|::)catch_unwind$"]}]
		}

		diagnose: {
			message:  "panic::catch_unwind is prohibited in first-party Rust"
			severity: "warning"
		}
	}
}
