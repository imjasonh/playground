// go_logger_field flags a struct field whose type is slog.Logger or
// clog.Logger, with or without a pointer.
//
// A logger on a struct is the one captured when the value was built.
// Pass a context into the function that logs, and read the logger
// with clog.FromContext. A function parameter, a result, and a local
// variable of that type are left alone. Litestream and other
// libraries take *slog.Logger because their API does.
//
// This checker has no types. A named type whose underlying type is
// slog.Logger is not flagged.

package go_logger_field

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_logger_field: schema.#Analyzer & {
	name:    "go_logger_field"
	version: "0.1.0"
	doc:     "Flag a struct field of type slog.Logger or clog.Logger"

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
}
