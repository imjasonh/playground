// go_httpresponse is a syntactic port of
// golang.org/x/tools/go/analysis/passes/httpresponse.
//
// `resp, err := http.Get(url)` followed immediately by
// `defer resp.Body.Close()` uses `resp` before the error check. When
// Get fails, `resp` is nil and the defer panics. Pasta matches that
// adjacent pair when the deferred close is on the same identifier.

package go_httpresponse

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_httpresponse: schema.#Analyzer & {
	name:    "go_httpresponse"
	version: "0.1.0"
	doc:     "Flag defer resp.Body.Close() before checking the error from http.Get"

	facts: {}

	rules: defer_before_err: {
		name: "defer_before_err"
		doc:  "defer resp.Body.Close immediately after http.Get uses resp before the error check"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: gopat.StmtListContainers
			adjacent: [
				{
					capture: "assign"
					pattern: {
						node: ["short_var_declaration", "assignment_statement"]
						fields: {
							left: {
								node: "expression_list"
								children: [{capture: "resp", pattern: gopat.Identifier}]
							}
							right: {
								node: "expression_list"
								children: [{
									pattern: gopat.PackageCall & {
										where: [
											{op: "eq", args: ["@pkg", "http"]},
											{op: "matches", args: ["@fn", "^(Get|Head|Post|PostForm)$"]},
										]
									}
								}]
							}
						}
					}
				},
				{
					capture: "def"
					pattern: {
						node: "defer_statement"
						children: [{
							node: "call_expression"
							fields: {
								function: {
									node: "selector_expression"
									fields: {
										operand: {
											node: "selector_expression"
											fields: {
												operand: {capture: "recv", pattern: gopat.Identifier}
												field:   {capture: "body", pattern: gopat.FieldIdentifier}
											}
										}
										field: {capture: "close", pattern: gopat.FieldIdentifier}
									}
								}
							}
							where: [
								{op: "eq", args: ["@body", "Body"]},
								{op: "eq", args: ["@close", "Close"]},
							]
						}]
					}
				},
			]
			where: [{op: "same_ident", args: ["@resp", "@recv"]}]
		}

		diagnose: {
			message:  "using @resp before checking for errors"
			severity: "warning"
		}
	}
}
