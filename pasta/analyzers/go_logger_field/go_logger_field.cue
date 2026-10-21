// go_logger_field flags a struct field or function parameter whose type
// is slog.Logger or clog.Logger, with or without a pointer.
//
// A logger on a struct is the one captured when the value was built.
// A logger parameter is the one the caller handed in. Pass a context
// into the function that logs, and read the logger with
// clog.FromContext. A result and a local variable of that type are
// left alone, so a function can build a logger and return it.
// Litestream takes *slog.Logger because that library's API does, and
// pasta skips that module.
//
// This checker has no types. A named type whose underlying type is
// slog.Logger is not flagged. A parenthesized result is the same syntax
// node as a parameter list; the rule keeps it by requiring the list to
// be the function's parameters, not its result.

package go_logger_field

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_logger_field: schema.#Analyzer & {
	name:    "go_logger_field"
	version: "0.2.0"
	doc:     "Flag a struct field or function parameter of type slog.Logger or clog.Logger"

	facts: {}

	rules: struct_field: {
		name: "struct_field"
		doc:  "struct field whose type is slog.Logger or clog.Logger"
		languages: [golang.Name]
		requires: []
		provides: []

		require_substring: [".Logger"]

		match: {
			node: "field_declaration"
			fields: type: {capture: "typ"}
			where: [{op: "matches", args: ["@typ", "^\\*?(slog|clog)\\.Logger$"]}]
		}

		diagnose: {
			message:  "logger stored on a struct; pass a context and read it with clog.FromContext"
			severity: "warning"
		}
	}

	rules: parameter: {
		name: "parameter"
		doc:  "function parameter whose type is slog.Logger or clog.Logger"
		languages: [golang.Name]
		requires: []
		provides: []

		require_substring: [".Logger"]

		match: {
			node: "parameter_declaration"
			fields: type: {capture: "typ"}
			where: [
				{op: "matches", args: ["@typ", "^\\*?(slog|clog)\\.Logger$"]},
				{op: "parent_field", args: ["@_root", "parameters"]},
			]
		}

		diagnose: {
			message:  "logger passed to a function; pass a context and read it with clog.FromContext"
			severity: "warning"
		}
	}
}
