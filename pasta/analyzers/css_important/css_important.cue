// css_important flags `!important` declarations. Overusing them makes
// cascade overrides unpredictable; prefer more specific selectors.

package css_important

import (
	"github.com/imjasonh/pasta/schema"
	csslang "github.com/imjasonh/pasta/lang/css"
)

css_important: schema.#Analyzer & {
	name:    "css_important"
	version: "0.1.0"
	doc:     "Flag !important declarations"
	facts: {}

	rules: important: {
		name:      "important"
		doc:       "Avoid !important"
		languages: [csslang.Name]
		requires: []
		provides: []

		match: {
			node: "important"
		}

		diagnose: {
			severity: "hint"
			message:  "avoid !important; prefer more specific selectors"
		}
	}
}
