// go_slog is a syntactic port of
// golang.org/x/tools/go/analysis/passes/slog.
//
// Key/value logging (`slog.Info("msg", "key")`) needs an even number
// of attributes after the message. Pasta flags a two-argument call
// whose second argument is a string literal — the usual missing
// value. `slog.Info("msg", slog.String(...))` is a single Attr and
// is left alone.

package go_slog

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_slog: schema.#Analyzer & {
	name:    "go_slog"
	version: "0.1.0"
	doc:     "Flag slog.Info(\"msg\", \"key\") missing a value"

	facts: {}

	rules: missing_value: {
		name: "missing_value"
		doc:  "string key with no matching value"
		languages: [golang.Name]
		requires: []
		provides: []

		match: gopat.PackageCall & {
			fields: arguments: {
				capture: "args"
				pattern: {
					node: "argument_list"
					children: [
						gopat.Any,
						{capture: "key", pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}},
					]
				}
			}
			where: [
				{op: "eq", args: ["@pkg", "slog"]},
				{op: "matches", args: ["@fn", "^(Debug|Info|Warn|Error)$"]},
				{op: "named_child_count", args: ["@args", "2"]},
			]
		}

		diagnose: {
			message:  "missing key or value in slog call"
			severity: "warning"
		}
	}
}
