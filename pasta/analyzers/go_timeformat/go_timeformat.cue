// go_timeformat is a syntactic port of
// golang.org/x/tools/go/analysis/passes/timeformat.
//
// `2006-02-01` looks like ISO 8601 (YYYY-MM-DD) but is YYYY-DD-MM in
// Go's reference layout. The correct date is `2006-01-02`. Pasta
// flags that substring in `time.Parse*`, `time.Format`, and any
// `.Format` call whose layout literal contains it.

package go_timeformat

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

_layoutLit: {
	capture: "lit"
	pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}
}

_fix: {
	rewrite: edits: [
		{within: "lit", token: "2006-02-01", replace_with: "2006-01-02"},
		{target: "lit", replacement: "@lit"},
	]
}

go_timeformat: schema.#Analyzer & {
	name:    "go_timeformat"
	version: "0.1.0"
	doc:     "Flag time layouts that use 2006-02-01 (YYYY-DD-MM) instead of 2006-01-02"
	facts: {}

	rules: {
		parse: {
			name: "parse"
			doc:  "time.Parse / ParseInLocation layout uses 2006-02-01"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [_layoutLit]
				}
				where: [
					{op: "eq", args: ["@pkg", "time"]},
					{op: "matches", args: ["@fn", "^Parse(InLocation)?$"]},
					{op: "matches", args: ["@lit", "2006-02-01"]},
				]
			}

			diagnose: {
				message:  "2006-02-01 should be 2006-01-02"
				severity: "warning"
			}

			rewrite: _fix.rewrite
		}

		format: {
			name: "format"
			doc:  "Time.Format layout uses 2006-02-01"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "call_expression"
				fields: {
					function: {
						node: "selector_expression"
						fields: field: {capture: "fn", pattern: gopat.FieldIdentifier}
					}
					arguments: {
						node: "argument_list"
						children: [_layoutLit]
					}
				}
				where: [
					{op: "eq", args: ["@fn", "Format"]},
					{op: "matches", args: ["@lit", "2006-02-01"]},
				]
			}

			diagnose: {
				message:  "2006-02-01 should be 2006-01-02"
				severity: "warning"
			}

			rewrite: _fix.rewrite
		}
	}
}
