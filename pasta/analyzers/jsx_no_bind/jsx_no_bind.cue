// jsx_no_bind flags `.bind(...)` inside JSX attribute expressions.
// `onClick={this.foo.bind(this)}` allocates a new function every
// render, defeating PureComponent / React.memo and causing needless
// child updates. Prefer a class property arrow, useCallback, or an
// inline arrow that doesn't rebind. Applies to .jsx/.js (javascript
// grammar) and .tsx. No auto-fix.

package jsx_no_bind

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

jsx_no_bind: schema.#Analyzer & {
	name:    "jsx_no_bind"
	version: "0.1.0"
	doc:     "Flag .bind() inside JSX attribute expressions"
	facts: {}

	rules: bind_in_jsx: {
		name:      "bind_in_jsx"
		doc:       "Flag .bind() in a JSX expression"
		languages: [jslang.Name, tsxlang.Name]
		requires: []
		provides: []

		match: {
			node: "jsx_expression"
			children: [{
				capture: "call"
				pattern: {
					node: "call_expression"
					fields: {
						function: {
							node: "member_expression"
							fields: {
								property: {capture: "prop", pattern: {node: "property_identifier"}}
							}
						}
					}
					where: [{op: "eq", args: ["@prop", "bind"]}]
				}
			}]
		}

		diagnose: {
			severity: "warning"
			message:  ".bind() in JSX creates a new function every render; use a stable callback"
		}
	}
}
