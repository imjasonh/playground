// go_import_alias flags a renamed import whose local name contains an
// underscore or a capital letter.
//
// The local name is the name code uses. Google Go style requires that
// name to follow package-name rules: lowercase, no underscores. Dot
// imports and blank imports are other rules.
// https://google.github.io/styleguide/go/decisions#import-renaming

package go_import_alias

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_import_alias: schema.#Analyzer & {
	name:    "go_import_alias"
	version: "0.1.0"
	doc:     "Flag import aliases that are not lowercase or that contain underscores"
	facts: {}

	rules: go_import_alias: {
		name:      "go_import_alias"
		doc:       "renamed import uses a non-package local name"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "import_spec"
			fields: name: {
				capture: "alias"
				pattern: {node: "package_identifier"}
			}
			where: [{op: "matches", args: ["@alias", "[_A-Z]"]}]
		}

		diagnose: {
			message:  "import alias must be lowercase and must not contain underscores"
			severity: "warning"
		}
	}
}
