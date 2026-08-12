// html_inline_handler flags inline DOM event-handler attributes
// (`onclick`, `onload`, …). They mix behavior into markup, complicate
// CSP, and are almost always replaceable with addEventListener in an
// external script. No auto-fix.

package html_inline_handler

import (
	"github.com/imjasonh/pasta/schema"
	htmllang "github.com/imjasonh/pasta/lang/html"
)

html_inline_handler: schema.#Analyzer & {
	name:    "html_inline_handler"
	version: "0.1.0"
	doc:     "Flag inline on* event-handler attributes"
	facts: {}

	rules: inline_handler: {
		name:      "inline_handler"
		doc:       "Flag onclick=/onload=/…"
		languages: [htmllang.Name]
		requires: []
		provides: []

		match: {
			node: "attribute"
			children: [{
				capture: "name"
				pattern: {node: "attribute_name"}
			}]
			where: [{op: "matches", args: ["@name", "(?i)^on[a-z]+$"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "inline event handler attribute; prefer addEventListener in a script"
		}
	}
}
