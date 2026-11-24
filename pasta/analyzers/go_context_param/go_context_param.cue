// go_context_param flags a parameter whose type is context.Context when
// the parameter list's first parameter is not.
//
// Google Go style: when a function takes a context, that parameter is
// first. The receiver does not count. A context in the result list
// does not count. A second context after a leading context is fine.
// A context mentioned only inside a nested function type belongs to
// that function, not the outer parameter list. HTTP handlers, streaming
// RPCs, and Test functions are the guide's exceptions; mark those
// lines pasta:ignore go_context_param.
// https://google.github.io/styleguide/go/decisions#contexts

package go_context_param

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_context_param: schema.#Analyzer & {
	name:    "go_context_param"
	version: "0.1.0"
	doc:     "Flag a context.Context parameter that is not first"
	facts: {}

	rules: go_context_param: {
		name:      "go_context_param"
		doc:       "context.Context is not the first parameter"
		languages: [golang.Name]
		requires: []
		provides: []

		require_substring: ["context.Context"]

		match: {
			node: "parameter_declaration"
			where: [
				{op: "matches", args: ["@_root", "(^|\\s)\\*?context\\.Context$"]},
				{op: "parent_field", args: ["@_root", "parameters"]},
				{op: "first_sibling_not_matches", args: ["@_root", "(^|\\s)\\*?context\\.Context$"]},
			]
		}

		diagnose: {
			message:  "context.Context parameter is not first"
			severity: "warning"
		}
	}
}
