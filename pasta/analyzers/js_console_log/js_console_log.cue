// js_console_log flags committed `console.log` / `console.debug` /
// `console.info` calls. They're fine while debugging; they almost
// never belong in production UI code (and drown real logging). Prefer
// a project logger, or delete the call. `console.warn` / `console.error`
// are left alone — those are often intentional. No auto-fix.

package js_console_log

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
)

js_console_log: schema.#Analyzer & {
	name:    "js_console_log"
	version: "0.1.0"
	doc:     "Flag console.log / console.debug / console.info"
	facts: {}

	rules: console_noise: {
		name:      "console_noise"
		doc:       "Flag noisy console.* debug calls"
		languages: [jslang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						object:   {capture: "obj", pattern: {node: "identifier"}}
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
			}
			where: [
				{op: "eq", args: ["@obj", "console"]},
				{op: "matches", args: ["@prop", "^(log|debug|info)$"]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "console.debug logging left in source; remove or use a real logger"
		}
	}
}
