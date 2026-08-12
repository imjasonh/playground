// html_img_alt flags `<img>` start tags that omit the `alt` attribute.
// Missing alt text fails WCAG 1.1.1 and hurts accessibility tooling.
// No auto-fix — the right alt text is content-specific (and decorative
// images should use `alt=""` intentionally).

package html_img_alt

import (
	"github.com/imjasonh/pasta/schema"
	htmllang "github.com/imjasonh/pasta/lang/html"
)

html_img_alt: schema.#Analyzer & {
	name:    "html_img_alt"
	version: "0.1.0"
	doc:     "Flag <img> tags missing an alt attribute"
	facts: {}

	rules: missing_alt: {
		name:      "missing_alt"
		doc:       "<img> without alt"
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
				{op: "matches", args: ["@name", "(?i)^img$"]},
				{op: "not_matches", args: ["@_root", "(?i)\\salt\\s*="]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "img tag should include alt text (use alt=\"\" for decorative images)"
		}
	}
}
