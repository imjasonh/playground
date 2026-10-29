// go_package_name flags a package clause that is not lowercase or
// that contains an underscore.
//
// Google Go style: package names are short, lowercase, and unbroken.
// A name that ends in `_test` may contain underscores. That covers
// black-box tests (`foo_test`) and integration tests
// (`linked_list_service_test`). The check looks at the whole clause
// (`package name`) so it does not depend on a grammar field name.
// https://google.github.io/styleguide/go/decisions#package-names

package go_package_name

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_package_name: schema.#Analyzer & {
	name:    "go_package_name"
	version: "0.1.0"
	doc:     "Flag package names that are not lowercase or that contain underscores"
	facts: {}

	rules: go_package_name: {
		name:      "go_package_name"
		doc:       "package clause is not a Google-style package name"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "package_clause"
			where: [
				{op: "matches", args: ["@_root", "[_A-Z]"]},
				{op: "not_matches", args: ["@_root", "_test$"]},
			]
		}

		diagnose: {
			message:  "package name must be lowercase and must not contain underscores"
			severity: "warning"
		}
	}
}
