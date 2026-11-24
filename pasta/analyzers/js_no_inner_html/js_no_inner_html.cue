// js_no_inner_html flags direct assignment to element.innerHTML.
// Clearing with an empty string (`el.innerHTML = ""`) is mechanically
// rewritten to `el.replaceChildren()`. Non-empty assignments (other than
// `DOMPurify.sanitize(...)`) are flagged because assigning unsanitized
// input to innerHTML is a common XSS vector.

package js_no_inner_html

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_langs: [jslang.Name, tslang.Name, tsxlang.Name]

_innerHtmlPattern: {
	node: "assignment_expression"
	fields: {
		left: {
			node: "member_expression"
			fields: {
				object:   {capture: "obj"}
				property: {capture: "prop", pattern: {node: "property_identifier"}}
			}
		}
		right: {capture: "rhs"}
	}
}

js_no_inner_html: schema.#Analyzer & {
	name:    "js_no_inner_html"
	version: "0.1.0"
	doc:     "Flag direct assignment to innerHTML (autofix empty-string clears to replaceChildren())"
	facts: {}

	rules: {
		clear_empty: {
			name:      "clear_empty"
			doc:       "Rewrite el.innerHTML = \"\" to el.replaceChildren()"
			languages: _langs
			requires: []
			provides: []

			match: _innerHtmlPattern & {
				where: [
					{op: "eq", args: ["@prop", "innerHTML"]},
					{op: "matches", args: ["@rhs", "^(\"\"|''|``)$"]},
				]
			}

			diagnose: {
				message:  "use replaceChildren() instead of assigning empty string to innerHTML"
				severity: "warning"
			}

			rewrite: edits: [{target: "_root", replacement: "@obj.replaceChildren()"}]
		}

		assignment: {
			name:      "assignment"
			doc:       "Assigning directly to innerHTML bypasses sanitization"
			languages: _langs
			requires: []
			provides: []

			match: _innerHtmlPattern & {
				where: [
					{op: "eq", args: ["@prop", "innerHTML"]},
					{op: "not_matches", args: ["@rhs", "^(\"\"|''|``)$"]},
					{op: "not_matches", args: ["@rhs", "^DOMPurify\\.sanitize\\("]},
				]
			}

			diagnose: {
				message:  "direct assignment to innerHTML can lead to XSS; use textContent, replaceChildren(), or a sanitizer"
				severity: "warning"
			}
		}
	}
}
