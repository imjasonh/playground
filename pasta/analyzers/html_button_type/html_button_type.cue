// html_button_type flags `<button>` tags that omit the `type` attribute.
// In HTML, the default type of a button is "submit", which can trigger
// unintended form submissions when nested in forms or dialogs.
// Explicitly specify type="button", type="submit", or type="reset".

package html_button_type

import (
	"github.com/imjasonh/pasta/schema"
	htmllang "github.com/imjasonh/pasta/lang/html"
)

html_button_type: schema.#Analyzer & {
	name:    "html_button_type"
	version: "0.1.0"
	doc:     "Flag <button> tags missing an explicit type attribute"
	facts: {}

	rules: missing_type: {
		name:      "missing_type"
		doc:       "<button> without type attribute defaults to type=\"submit\""
		languages: [htmllang.Name]
		requires: []
		provides: []

		match: {
			node: "start_tag"
			children: [{
				capture: "name"
				pattern: {node: "tag_name"}
			}]
			where: [
				{op: "matches", args: ["@name", "(?i)^button$"]},
				{op: "not_matches", args: ["@_root", "(?i)\\stype\\s*="]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "<button> missing explicit type attribute (defaults to type=\"submit\"); add type=\"button\", type=\"submit\", or type=\"reset\""
		}
	}
}
