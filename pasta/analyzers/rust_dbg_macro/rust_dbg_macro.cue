// rust_dbg_macro flags committed `dbg!(...)` macro invocations. The
// `dbg!` macro is a debugging convenience that prints to stderr and
// returns its argument; it almost never belongs in committed code.
// Often clippy's `dbg_macro` lint is left at warn-level by default; we
// fire as a hard error so it shows up in CI.
//
// No auto-fix: trimming `dbg!(…)` bytes is unsafe for `dbg!()` (empty)
// and multi-arg `dbg!(a, b)`.

package rust_dbg_macro

import (
	"github.com/imjasonh/pasta/schema"
	rustlang "github.com/imjasonh/pasta/lang/rust"
)

rust_dbg_macro: schema.#Analyzer & {
	name:    "rust_dbg_macro"
	version: "0.1.0"
	doc:     "Flag committed dbg!() invocations"
	facts: {}

	rules: dbg_call: {
		name: "dbg_call"
		doc:  "dbg!() should not appear in committed code"
		languages: [rustlang.Name]
		requires: []
		provides: []

		match: {
			node: "macro_invocation"
			fields: {
				macro: {capture: "name"}
			}
			where: [{op: "eq", args: ["@name", "dbg"]}]
		}

		diagnose: {
			message:  "dbg!() macro invocation — remove before committing"
			severity: "error"
		}
	}
}
