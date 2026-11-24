// rust_todo_macro flags `todo!()` and `unimplemented!()` macro
// invocations. Both macros panic unconditionally at runtime and should
// not be left in shipping code.

package rust_todo_macro

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

rust_todo_macro: schema.#Analyzer & {
	name:    "rust_todo_macro"
	version: "0.1.0"
	doc:     "Flag todo!() and unimplemented!() macro invocations"
	facts: {}

	rules: todo: {
		name:      "todo"
		doc:       "Flag todo!() and unimplemented!() macros"
		languages: [rustlang.Name]
		requires: []
		provides: []

		match: {
			node: "macro_invocation"
			fields: {
				macro: {capture: "macro_name"}
			}
			where: [
				{op: "matches", args: ["@macro_name", "^(todo|unimplemented)$"]},
			]
		}

		diagnose: {
			message:  "`@macro_name!()` left in code; complete implementation before shipping"
			severity: "warning"
		}
	}
}
