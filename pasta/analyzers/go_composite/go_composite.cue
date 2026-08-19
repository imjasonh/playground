// go_composite is a syntactic port of
// golang.org/x/tools/go/analysis/passes/composite.
//
// Vet flags unkeyed composite literals of imported struct types
// (`pkg.T{a, b}` instead of `pkg.T{A: a, B: b}`). Without types Pasta
// approximates that by requiring a `qualified_type` (`pkg.T`) whose
// literal's first element is not a keyed field. Local types such as
// `T{a, b}` and slices such as `[]int{1}` are left alone.

package go_composite

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_composite: schema.#Analyzer & {
	name:    "go_composite"
	version: "0.1.0"
	doc:     "Flag unkeyed composite literals of imported types"

	facts: {}

	rules: unkeyed_imported: {
		name: "unkeyed_imported"
		doc:  "pkg.T{a, b} should use keyed fields"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "composite_literal"
			fields: {
				type: {pattern: {node: "qualified_type"}}
				body: {
					node: "literal_value"
					children: [{capture: "elem"}]
				}
			}
			where: [{op: "node_is_not", args: ["@elem", "keyed_element"]}]
		}

		diagnose: {
			message:  "unkeyed composite literal"
			severity: "warning"
		}
	}
}
