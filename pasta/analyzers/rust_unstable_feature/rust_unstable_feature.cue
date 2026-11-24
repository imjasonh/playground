// rust_unstable_feature flags #![feature(...)] and #[feature(...)].
//
// Google Rust style: don't use unstable features. Android, Chrome, and
// Fuchsia have review exceptions. This repo is none of those. A cfg
// flag (`#[cfg(feature = "x")]`) is not an unstable language feature.
// https://google.github.io/styleguide/rustguide.html#unstable-features

package rust_unstable_feature

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

rust_unstable_feature: schema.#Analyzer & {
	name:    "rust_unstable_feature"
	version: "0.1.0"
	doc:     "Flag #![feature] and #[feature]"
	facts: {}

	rules: rust_unstable_feature: {
		name:      "rust_unstable_feature"
		doc:       "unstable language feature attribute"
		languages: [rustlang.Name]
		requires: []
		provides: []

		require_substring: ["feature"]

		match: {
			node: ["attribute_item", "inner_attribute_item"]
			where: [{op: "matches", args: ["@_root", "^#!?\\[\\s*feature\\b"]}]
		}

		diagnose: {
			message:  "unstable Rust feature; use stable Rust"
			severity: "warning"
		}
	}
}
