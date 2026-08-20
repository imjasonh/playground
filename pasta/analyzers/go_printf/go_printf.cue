// go_printf is a syntactic port of
// golang.org/x/tools/go/analysis/passes/printf.
//
// Pasta cannot parse format strings the way vet does. It flags
// `fmt.Printf` / `Sprintf` / `Errorf` calls whose only argument is a
// string containing a non-`%%` verb — a missing operand. Extra
// arguments, `*` widths, and indexed verbs are out of reach.

package go_printf

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_printf: schema.#Analyzer & {
	name:    "go_printf"
	version: "0.1.0"
	doc:     "Flag fmt.Printf/Sprintf/Errorf with a verb but no operand"

	facts: {}

	rules: missing_arg: {
		name: "missing_arg"
		doc:  "format verb with only the format string argument"
		languages: [golang.Name]
		requires: []
		provides: []

		match: gopat.PackageCall & {
			fields: arguments: {
				capture: "args"
				pattern: {
					node: "argument_list"
					children: [{
						capture: "fmt"
						pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}
					}]
				}
			}
			where: [
				{op: "eq", args: ["@pkg", "fmt"]},
				{op: "matches", args: ["@fn", "^(Printf|Sprintf|Errorf)$"]},
				{op: "named_child_count", args: ["@args", "1"]},
				{op: "matches", args: ["@fmt", "%[#0+-]*[0-9.]*[sdqveEfFgGtxXpbwT]"]},
			]
		}

		diagnose: {
			message:  "fmt.@fn format has a verb but no operand"
			severity: "warning"
		}
	}
}
