// rust_glob_import flags a glob import.
//
// Google Rust style forbids glob imports, with these exceptions the
// checker leaves alone:
//
//   - `use super::*` for inline modules and tests
//   - a path ending in `prelude`
//   - `pub` / `pub(crate)` re-exports (`pub use submodule::*` is allowed
//     for non-leaf modules; leaf-ness is not visible here)
//
// `use enum::*` inside a function that is mostly about that enum is
// also allowed. That case is not distinguishable as syntax. Suppress
// it with pasta:ignore rust_glob_import.
// https://google.github.io/styleguide/rustguide.html

package rust_glob_import

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

rust_glob_import: schema.#Analyzer & {
	name:    "rust_glob_import"
	version: "0.1.0"
	doc:     "Flag glob imports other than super::*, prelude::*, and pub use"
	facts: {}

	rules: rust_glob_import: {
		name:      "rust_glob_import"
		doc:       "glob import other than the guide's exceptions"
		languages: [rustlang.Name]
		requires: []
		provides: []

		require_substring: ["::*"]

		match: {
			node: "use_declaration"
			where: [
				{op: "matches", args: ["@_root", "::\\s*\\*"]},
				{op: "not_matches", args: ["@_root", "^\\s*pub\\b"]},
				{op: "not_matches", args: ["@_root", "\\bsuper\\s*::\\s*\\*"]},
				{op: "not_matches", args: ["@_root", "\\bprelude\\s*::\\s*\\*"]},
			]
		}

		diagnose: {
			message:  "glob import; name the items, or keep super::*, a prelude, or pub use"
			severity: "warning"
		}
	}
}
