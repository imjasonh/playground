// go_context_field flags a struct field of type context.Context.
//
// Google Go style: do not store a context on a struct. Pass it to each
// method that needs it. The guide's exception is a method signature
// that must match an interface outside your control, which is not a
// struct field.
// https://google.github.io/styleguide/go/decisions#contexts

package go_context_field

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_context_field: schema.#Analyzer & {
	name:    "go_context_field"
	version: "0.1.0"
	doc:     "Flag a struct field of type context.Context"
	facts: {}

	rules: go_context_field: {
		name:      "go_context_field"
		doc:       "struct field stores a context.Context"
		languages: [golang.Name]
		requires: []
		provides: []

		require_substring: ["context.Context"]

		match: {
			node: "field_declaration"
			fields: type: {capture: "typ"}
			where: [{op: "matches", args: ["@typ", "^\\*?context\\.Context$"]}]
		}

		diagnose: {
			message:  "context.Context stored on a struct; pass it as a parameter"
			severity: "warning"
		}
	}
}
