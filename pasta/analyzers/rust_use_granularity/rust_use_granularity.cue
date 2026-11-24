// rust_use_granularity flags a `use` list that contains `::`.
//
// Google Rust style corresponds to rustfmt `imports_granularity = "Module"`:
// a use list imports items from one module, so the path inside the
// braces has no `::`. `bar::*` is a glob import and is rust_glob_import's
// job; a list that only contains globs still matches here because the
// `::` is visible. Suppress one of the two when they are the same decision.
// https://google.github.io/styleguide/rustguide.html#use-statement

package rust_use_granularity

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

rust_use_granularity: schema.#Analyzer & {
	name:    "rust_use_granularity"
	version: "0.1.0"
	doc:     "Flag a use list that imports from more than one module"
	facts: {}

	rules: rust_use_granularity: {
		name:      "rust_use_granularity"
		doc:       "use list contains a nested path"
		languages: [rustlang.Name]
		requires: []
		provides: []

		match: {
			node: "use_list"
			where: [{op: "matches", args: ["@_root", "::"]}]
		}

		diagnose: {
			message:  "use list imports from more than one module; split it"
			severity: "warning"
		}
	}
}
