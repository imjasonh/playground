// html_lang flags `<html>` start tags that omit the `lang` attribute.
// Without it, screen readers guess the document language. WCAG 3.1.1
// requires `lang` on the root. No auto-fix — the right BCP 47 tag is
// content-specific (`en`, `en-US`, …).

package html_lang

import (
	"github.com/imjasonh/pasta/schema"
	htmllang "github.com/imjasonh/pasta/lang/html"
)

html_lang: schema.#Analyzer & {
	name:    "html_lang"
	version: "0.1.0"
	doc:     "Flag <html> tags missing a lang attribute"
	facts: {}

	rules: missing_lang: {
		name:      "missing_lang"
		doc:       "<html> without lang"
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
				{op: "matches", args: ["@name", "(?i)^html$"]},
				{op: "not_matches", args: ["@_root", "(?i)\\slang\\s*="]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "html tag is missing a lang attribute (for example lang=\"en\")"
		}
	}
}
