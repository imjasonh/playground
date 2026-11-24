// js_no_default_export flags `export default`.
//
// Google JavaScript and TypeScript style require named exports. A
// default export has no canonical name, so importers invent one.
// Tool configs (jest.config.js, playwright.config.js, and other
// `*.config.*` files) are required by those tools to default-export.
// .pasta/pasta.cue disables this rule on those paths.
// https://google.github.io/styleguide/jsguide.html#named-vs-default-exports
// https://google.github.io/styleguide/tsguide.html

package js_no_default_export

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

js_no_default_export: schema.#Analyzer & {
	name:    "js_no_default_export"
	version: "0.1.0"
	doc:     "Flag export default"
	facts: {}

	rules: js_no_default_export: {
		name:      "js_no_default_export"
		doc:       "default export"
		languages: [jslang.Name, tslang.Name, tsxlang.Name]
		requires: []
		provides: []

		require_substring: ["export default"]

		match: {
			node: "export_statement"
			where: [{op: "matches", args: ["@_root", "^export\\s+default\\b"]}]
		}

		diagnose: {
			message:  "default export; use a named export"
			severity: "warning"
		}
	}
}
