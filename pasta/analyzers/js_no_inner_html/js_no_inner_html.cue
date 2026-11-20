// js_no_inner_html flags direct assignment to element.innerHTML.
// Assigning unsanitized input to innerHTML is a common vector for XSS.
// Prefer using textContent, replaceChildren(), or an explicit sanitizer.

package js_no_inner_html

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_langs: [jslang.Name, tslang.Name, tsxlang.Name]

js_no_inner_html: schema.#Analyzer & {
	name:    "js_no_inner_html"
	version: "0.1.0"
	doc:     "Flag direct assignment to innerHTML (XSS risk)"
	facts: {}

	rules: assignment: {
		name:      "assignment"
		doc:       "Assigning directly to innerHTML bypasses sanitization"
		languages: _langs
		requires: []
		provides: []

		match: {
			node: "assignment_expression"
			fields: {
				left: {
					node: "member_expression"
					fields: {
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
			}
			where: [
				{op: "eq", args: ["@prop", "innerHTML"]},
			]
		}

		diagnose: {
			message:  "direct assignment to innerHTML can lead to XSS; use textContent, replaceChildren(), or a sanitizer"
			severity: "hint"
		}
	}
}
