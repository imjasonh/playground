// go_unmarshal is a syntactic port of
// golang.org/x/tools/go/analysis/passes/unmarshal.
//
// `json.Unmarshal` and `xml.Unmarshal` need a pointer as the second
// argument. Pasta flags when that argument is a plain identifier
// (not `&x` and not a call). This misses interface values that are
// already pointers and flags some valid pointer variables — the
// common mistake is still `Unmarshal(b, v)` instead of `&v`.

package go_unmarshal

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_unmarshal: schema.#Analyzer & {
	name:    "go_unmarshal"
	version: "0.1.0"
	doc:     "Flag json.Unmarshal / xml.Unmarshal with a non-address second argument"

	facts: {}

	rules: ident_target: {
		name: "ident_target"
		doc:  "Unmarshal(b, v) should be Unmarshal(b, &v) when v is not already a pointer"
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
				{op: "matches", args: ["@pkg", "^(json|xml)$"]},
				{op: "eq", args: ["@fn", "Unmarshal"]},
			]
		}

		diagnose: {
			message:  "call of Unmarshal passes non-pointer as second argument"
			severity: "warning"
		}

		rewrite: edits: [{
			position: "before"
			anchor:   "dst"
			text:     "&"
		}]
	}
}
