// go_fmtprint flags fmt.Print, fmt.Println, and fmt.Printf.
//
// Those calls write to standard output. A log belongs in slog, with
// a message and attributes. clog.Fatal and log.Fatal are the calls
// that log and then exit. slog has no equivalent.
//
// A single string argument is rewritten to slog.Info. The other
// shapes stay as diagnostics: a format string and its operands do
// not become attributes without a format parser, and this checker
// has no types.
//
// fmt.Fprint, fmt.Fprintln, and fmt.Fprintf are not flagged. They
// write to a caller-supplied writer, which is how a command prints
// its result and how code formats into a buffer.

package go_fmtprint

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

#fns: "^(Print|Println|Printf)$"

#diagnose: {
	message:  "fmt print; use slog with attributes, or log.Fatal or clog.Fatal when the process exits"
	severity: "warning"
}

// #where is the shared fmt.Print / Println / Printf check, plus any
// extra predicates. CUE rejects list addition, so the shared pair is
// written out here once.
#where: {
	extra: [...{op: string, args: [...string | [...string]]}]
	out: [
		{op: "eq", args: ["@pkg", "fmt"]},
		{op: "matches", args: ["@fn", #fns]},
		for p in extra {p},
	]
}

go_fmtprint: schema.#Analyzer & {
	name:    "go_fmtprint"
	version: "0.1.0"
	doc:     "Flag fmt.Print, fmt.Println, and fmt.Printf; rewrite a single string to slog.Info"

	facts: {}

	rules: {
		literal_message: {
			name: "literal_message"
			doc:  "fmt.Println(\"msg\") and the other single-string prints"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					capture: "args"
					pattern: {
						node: "argument_list"
						children: [{
							capture: "msg"
							pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}
						}]
					}
				}
				where: (#where & {extra: [{op: "named_child_count", args: ["@args", "1"]}]}).out
			}

			diagnose: #diagnose

			rewrite: edits: [{
				target:      "_root"
				replacement: "slog.Info(@msg)"
			}]
		}

		bare: {
			name: "bare"
			doc:  "fmt.Println() and the other calls with no arguments"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					capture: "args"
					pattern: {node: "argument_list"}
				}
				where: (#where & {extra: [{op: "named_child_count", args: ["@args", "0"]}]}).out
			}

			diagnose: #diagnose

			rewrite: edits: [{
				target:      "_root"
				replacement: "slog.Info(\"\")"
			}]
		}

		value: {
			name: "value"
			doc:  "a single non-string argument, which slog needs a message and an attribute for"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					capture: "args"
					pattern: {
						node:     "argument_list"
						children: [{capture: "arg"}]
					}
				}
				where: (#where & {extra: [
					{op: "named_child_count", args: ["@args", "1"]},
					{op: "node_is_not", args: ["@arg", ["interpreted_string_literal", "raw_string_literal"]]},
				]}).out
			}

			diagnose: #diagnose
		}

		args: {
			name: "args"
			doc:  "two or more arguments, including printf-style calls"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					node:     "argument_list"
					children: [gopat.Any, gopat.Any]
				}
				where: (#where & {extra: []}).out
			}

			diagnose: #diagnose
		}
	}
}
