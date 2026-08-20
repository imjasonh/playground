// js_debugger flags `debugger;` statements. They pause the JS engine
// when a debugger is attached and are almost never meant to ship.
// ESLint `no-debugger` covers the same ground. No auto-fix — deleting
// the statement is usually right, but a leftover breakpoint can be a
// signal that nearby code is still under development.

package js_debugger

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
	tslang "github.com/imjasonh/pasta/lang/typescript"
)

js_debugger: schema.#Analyzer & {
	name:    "js_debugger"
	version: "0.1.0"
	doc:     "Flag debugger statements left in committed code"
	facts: {}

	rules: debugger_stmt: {
		name: "debugger_stmt"
		doc:  "debugger; pauses the engine when a debugger is attached"
		languages: [jslang.Name, tslang.Name, tsxlang.Name]
		requires: []
		provides: []

		match: {
			node: "debugger_statement"
		}

		diagnose: {
			severity: "warning"
			message:  "debugger statement; remove before committing"
		}
	}
}
