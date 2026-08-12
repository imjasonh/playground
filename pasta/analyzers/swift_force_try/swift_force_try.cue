// swift_force_try flags `try!` expressions. Like force-unwrap, try!
// crashes the process when the call throws — almost always a sign the
// author hasn't decided how to handle the error. Prefer `try?`,
// `do/catch`, or propagating `try`. No auto-fix.

package swift_force_try

import (
	"github.com/imjasonh/pasta/schema"
	swlang "github.com/imjasonh/pasta/lang/swift"
)

swift_force_try: schema.#Analyzer & {
	name:    "swift_force_try"
	version: "0.1.0"
	doc:     "Flag try! force-try expressions"
	facts: {}

	rules: force_try: {
		name:      "force_try"
		doc:       "Flag try!"
		languages: [swlang.Name]
		requires: []
		provides: []

		match: {
			node: "try_expression"
			where: [{op: "matches", args: ["@_root", "^try!"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "try! will crash if the call throws; prefer try?, do/catch, or propagating try"
		}
	}
}
