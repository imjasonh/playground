// css_empty_block flags `{}` rule bodies with no declarations.
// Stylelint `block-no-empty` covers the same ground. Comment-only
// bodies count as empty because pasta's `empty` predicate skips
// comment nodes. No auto-fix — the selector may be a placeholder
// the author still wants to keep.

package css_empty_block

import (
	"github.com/imjasonh/pasta/schema"
	csslang "github.com/imjasonh/pasta/lang/css"
)

css_empty_block: schema.#Analyzer & {
	name:    "css_empty_block"
	version: "0.1.0"
	doc:     "Flag empty CSS blocks"
	facts: {}

	rules: empty_block: {
		name:      "empty_block"
		doc:       "Flag {} with no declarations"
		languages: [csslang.Name]
		requires: []
		provides: []

		match: {
			node: "block"
			where: [{op: "empty", args: ["@_root"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "empty CSS block; add a declaration or remove the rule"
		}
	}
}
