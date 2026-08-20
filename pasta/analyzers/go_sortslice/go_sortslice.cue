// go_sortslice is a syntactic port of
// golang.org/x/tools/go/analysis/passes/sortslice.
//
// `sort.Slice` requires `func(i, j int) bool`. Pasta flags a function
// literal with no parameters, or with a single parameter (`func(int)`
// or `func(i int)`). `func(i, j int)` is one parameter declaration
// with two names and is accepted; `func(int, int)` is two
// declarations and is accepted. Named function values are not
// checked.

package go_sortslice

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

_oneDecl: {
	_n: string

	out: {
		languages: [golang.Name]
		requires: []
		provides: []

		match: gopat.PackageCall & {
			fields: arguments: {
				node: "argument_list"
				children: [
					gopat.Any,
					{
						node: "func_literal"
						fields: parameters: {
							capture: "params"
							pattern: {
								node: "parameter_list"
								children: [{
									capture: "p"
									pattern: {node: "parameter_declaration"}
								}]
							}
						}
					},
				]
			}
			where: [
				{op: "eq", args: ["@pkg", "sort"]},
				{op: "eq", args: ["@fn", "Slice"]},
				{op: "named_child_count", args: ["@params", "1"]},
				{op: "named_child_count", args: ["@p", _n]},
			]
		}

		diagnose: {
			message:  "sort.Slice's comparison function must have two parameters"
			severity: "warning"
		}
	}
}

go_sortslice: schema.#Analyzer & {
	name:    "go_sortslice"
	version: "0.1.0"
	doc:     "Flag sort.Slice comparison functions that do not take two parameters"
	facts: {}

	rules: {
		zero_params: {
			name: "zero_params"
			doc:  "sort.Slice(s, func() bool)"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [
						gopat.Any,
						{
							node: "func_literal"
							fields: parameters: {capture: "params"}
						},
					]
				}
				where: [
					{op: "eq", args: ["@pkg", "sort"]},
					{op: "eq", args: ["@fn", "Slice"]},
					{op: "named_child_count", args: ["@params", "0"]},
				]
			}

			diagnose: {
				message:  "sort.Slice's comparison function must have two parameters"
				severity: "warning"
			}
		}

		one_unnamed: (_oneDecl & {_n: "1"}).out & {
			name: "one_unnamed"
			doc:  "sort.Slice(s, func(int) bool)"
		}
		one_named: (_oneDecl & {_n: "2"}).out & {
			name: "one_named"
			doc:  "sort.Slice(s, func(i int) bool)"
		}
	}
}
