// go_dot_import flags `import . "pkg"`.
//
// Google Go style forbids dot imports. A dot import drops the package
// name, so a reader cannot tell which package an identifier comes from.
// https://google.github.io/styleguide/go/decisions#import-dot

package go_dot_import

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_dot_import: schema.#Analyzer & {
	name:    "go_dot_import"
	version: "0.1.0"
	doc:     "Flag import . \"pkg\""
	facts: {}

	rules: go_dot_import: {
		name:      "go_dot_import"
		doc:       "dot import hides the package name"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "import_spec"
			fields: name: {node: "dot"}
		}

		diagnose: {
			message:  "dot import; use a normal import and qualify names"
			severity: "warning"
		}
	}
}
