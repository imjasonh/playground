// go_unsafeptr is a syntactic port of
// golang.org/x/tools/go/analysis/passes/unsafeptr.
//
// Converting a `uintptr` back to `unsafe.Pointer` is invalid unless
// it happens in the same expression that produced the uintptr. Pasta
// flags `unsafe.Pointer(uintptr(...))` — the classic invalid
// round-trip. Valid uses such as `unsafe.Pointer(&x)` are left alone.

package go_unsafeptr

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_unsafeptr: schema.#Analyzer & {
	name:    "go_unsafeptr"
	version: "0.1.0"
	doc:     "Flag unsafe.Pointer(uintptr(...)) conversions"

	facts: {}

	rules: uintptr_roundtrip: {
		name: "uintptr_roundtrip"
		doc:  "unsafe.Pointer(uintptr(x)) is an invalid conversion"
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "selector_expression"
					fields: {
						operand: {capture: "pkg", pattern: gopat.Identifier}
						field:   {capture: "fn", pattern: gopat.FieldIdentifier}
					}
				}
				arguments: {
					node: "argument_list"
					children: [{
						node: "call_expression"
						fields: function: {capture: "inner", pattern: {node: "identifier"}}
						where: [{op: "eq", args: ["@inner", "uintptr"]}]
					}]
				}
			}
			where: [
				{op: "eq", args: ["@pkg", "unsafe"]},
				{op: "eq", args: ["@fn", "Pointer"]},
			]
		}

		diagnose: {
			message:  "possible misuse of unsafe.Pointer"
			severity: "warning"
		}
	}
}
