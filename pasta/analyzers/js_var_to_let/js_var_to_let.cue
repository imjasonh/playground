// js_var_to_let flags `var` declarations in favor of `let`. `var` is
// function-scoped and hoisted; `let` is block-scoped and not. ESLint's
// `no-var` flags this.
//
// Report-only by default: a structural `var`→`let` rewrite is a
// footgun without scope analysis. Intentional redeclarations like
// `var { ctx, spanToStart } = ctx.span(...)` break under `let`, as do
// cases that rely on hoisting / function scoping. Pasta does not yet
// ship a safe_rewrite predicate ("binding not already in scope"), so
// this rule diagnoses only — review and fix by hand (or layer a
// scope-aware rewrite later).

package js_var_to_let

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
)

js_var_to_let: schema.#Analyzer & {
	name:    "js_var_to_let"
	version: "0.2.0"
	doc:     "Flag var declarations (prefer let); report-only — no autofix"
	facts: {}

	rules: var_to_let: {
		name:      "var_to_let"
		doc:       "var x — prefer let (no autofix; scope-sensitive)"
		languages: [jslang.Name]
		requires: []
		provides: []

		match: {
			node: "variable_declaration"
		}

		diagnose: {
			message:  "use `let` instead of `var` (review scope before changing — redeclaration / hoisting may break)"
			severity: "warning"
		}
	}
}
