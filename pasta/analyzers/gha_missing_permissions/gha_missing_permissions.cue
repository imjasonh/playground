// gha_missing_permissions flags GitHub Actions workflow files that
// declare `jobs:` but omit a top-level `permissions:` block.
// Workflows without an explicit permissions declaration default to
// broad repository token permissions.

package gha_missing_permissions

import (
	"github.com/imjasonh/pasta/schema"
	yamllang "github.com/imjasonh/pasta/lang/yaml"
)

gha_missing_permissions: schema.#Analyzer & {
	name:    "gha_missing_permissions"
	version: "0.1.0"
	doc:     "Flag GitHub Actions workflows missing a top-level permissions: block"
	facts: {}

	rules: missing_permissions: {
		name:      "missing_permissions"
		doc:       "Workflows without top-level permissions inherit default write permissions"
		languages: [yamllang.Name]
		requires: []
		provides: []
		require_substring: ["jobs:"]

		match: {
			node: "document"
			where: [
				{op: "matches", args: ["@_root", "(?m)^jobs:"]},
				{op: "not_matches", args: ["@_root", "(?m)^permissions\\s*:"]},
			]
		}

		diagnose: {
			severity: "hint"
			message:  "workflow lacks a top-level permissions: definition; specify explicit minimal permissions"
		}
	}
}
