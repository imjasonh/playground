// go_errorsas is a syntactic port of
// golang.org/x/tools/go/analysis/passes/errorsas.
//
// `errors.As` needs a pointer to a variable that can hold an error
// value. The usual mistake is `errors.As(err, e)` instead of `&e`.
// Pasta flags a second argument that is a plain identifier.

package go_errorsas

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_errorsas: schema.#Analyzer & {
	name:    "go_errorsas"
	version: "0.1.0"
	doc:     "Flag errors.As with a non-address second argument"

	facts: {}

	rules: ident_target: {
		name: "ident_target"
		doc:  "errors.As(err, e) should be errors.As(err, &e)"
		languages: [golang.Name]
		requires: []
		provides: []

		match: gopat.PackageCall & {
			fields: arguments: {
				node: "argument_list"
				children: [
					{},
					{capture: "dst", pattern: gopat.Identifier},
				]
			}
			where: [
				{op: "eq", args: ["@pkg", "errors"]},
				{op: "eq", args: ["@fn", "As"]},
			]
		}

		diagnose: {
			message:  "second argument to errors.As must be a non-nil pointer"
			severity: "warning"
		}

		rewrite: edits: [{
			position: "before"
			anchor:   "dst"
			text:     "&"
		}]
	}
}
