// go_nilfunc is a syntactic port of
// golang.org/x/tools/go/analysis/passes/nilfunc.
//
// Comparing a function value to nil is always true (`!=`) or always
// false (`==`). Pasta tags function declarations, then flags
// identifier comparisons against nil that share that name. Name-only
// facts cannot distinguish a variable that shadows the function.

package go_nilfunc

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_nilfunc: schema.#Analyzer & {
	name:    "go_nilfunc"
	version: "0.1.0"
	doc:     "Flag comparisons of a function to nil"

	facts: {
		is_func: {kind: "is_func"}
	}

	rules: {
		mark_funcs: {
			name:      "mark_funcs"
			doc:       "Tag function declaration names"
			languages: [golang.Name]
			requires: []
			provides: ["is_func"]

			match: {
				node: "function_declaration"
				fields: name: {capture: "fn_name"}
			}

			emit: [{
				fact:   "is_func"
				attach: "fn_name"
			}]
		}

		cmp_left: {
			name:      "cmp_left"
			doc:       "f == nil / f != nil where f is a function"
			languages: [golang.Name]
			requires: ["is_func"]
			provides: []

			match: {
				node: "binary_expression"
				fields: {
					left:     {capture: "fn", pattern: gopat.Identifier}
					operator: {capture: "op"}
					right: {node: "nil"}
				}
				where: [
					{op: "matches", args: ["@op", "^(==|!=)$"]},
					{op: "has_fact", args: ["@fn", "is_func"]},
				]
			}

			diagnose: {
				message:  "comparison of function @fn to nil is always true or false"
				severity: "warning"
			}
		}

		cmp_right: {
			name:      "cmp_right"
			doc:       "nil == f / nil != f where f is a function"
			languages: [golang.Name]
			requires: ["is_func"]
			provides: []

			match: {
				node: "binary_expression"
				fields: {
					left:     gopat.Nil
					operator: {capture: "op"}
					right:    {capture: "fn", pattern: gopat.Identifier}
				}
				where: [
					{op: "matches", args: ["@op", "^(==|!=)$"]},
					{op: "has_fact", args: ["@fn", "is_func"]},
				]
			}

			diagnose: {
				message:  "comparison of function @fn to nil is always true or false"
				severity: "warning"
			}
		}
	}
}
