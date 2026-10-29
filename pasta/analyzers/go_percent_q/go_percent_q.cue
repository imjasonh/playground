// go_percent_q flags a fmt format string that quotes %s by hand.
//
// Google Go style uses the %q verb instead of quotation marks around
// %s. %q emits a double-quoted Go string, with escapes.
// https://google.github.io/styleguide/go/best-practices#fmt-sprintf
//
// The match is the source text of the literal. An interpreted string
// spells the quotes as \", and a raw string spells them as ".
// A format string that is only "%s" is not a quoted verb.

package go_percent_q

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

// Regexp for a backslash, a quote, %s, a backslash, and a quote.
#quotedInInterpreted: #"\\"%s\\""#

// Regexp for a quote, %s, and a quote. Used on raw string literals,
// whose delimiters are backticks.
#quotedInRaw: ##""%s""##

#diagnose: {
	message:  "use %q instead of a quoted %s"
	severity: "warning"
}

go_percent_q: schema.#Analyzer & {
	name:    "go_percent_q"
	version: "0.1.0"
	doc:     "Flag fmt formats that quote %s by hand; use %q"
	facts: {}

	rules: {
		printf_interpreted: {
			name:      "use_percent_q"
			doc:       "Printf, Sprintf, or Errorf quotes %s in an interpreted string"
			languages: [golang.Name]
			requires: []
			provides: []
			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [{
						capture: "fmtstr"
						pattern: {node: "interpreted_string_literal"}
					}]
				}
				where: [
					{op: "eq", args: ["@pkg", "fmt"]},
					{op: "matches", args: ["@fn", "^(Printf|Sprintf|Errorf)$"]},
					{op: "matches", args: ["@fmtstr", #quotedInInterpreted]},
				]
			}
			diagnose: #diagnose
		}
		printf_raw: {
			name:      "use_percent_q"
			doc:       "Printf, Sprintf, or Errorf quotes %s in a raw string"
			languages: [golang.Name]
			requires: []
			provides: []
			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [{
						capture: "fmtstr"
						pattern: {node: "raw_string_literal"}
					}]
				}
				where: [
					{op: "eq", args: ["@pkg", "fmt"]},
					{op: "matches", args: ["@fn", "^(Printf|Sprintf|Errorf)$"]},
					{op: "matches", args: ["@fmtstr", #quotedInRaw]},
				]
			}
			diagnose: #diagnose
		}
		fprintf_interpreted: {
			name:      "use_percent_q"
			doc:       "Fprintf or Appendf quotes %s in an interpreted string"
			languages: [golang.Name]
			requires: []
			provides: []
			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [
						gopat.Any,
						{
							capture: "fmtstr"
							pattern: {node: "interpreted_string_literal"}
						},
					]
				}
				where: [
					{op: "eq", args: ["@pkg", "fmt"]},
					{op: "matches", args: ["@fn", "^(Fprintf|Appendf)$"]},
					{op: "matches", args: ["@fmtstr", #quotedInInterpreted]},
				]
			}
			diagnose: #diagnose
		}
		fprintf_raw: {
			name:      "use_percent_q"
			doc:       "Fprintf or Appendf quotes %s in a raw string"
			languages: [golang.Name]
			requires: []
			provides: []
			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [
						gopat.Any,
						{
							capture: "fmtstr"
							pattern: {node: "raw_string_literal"}
						},
					]
				}
				where: [
					{op: "eq", args: ["@pkg", "fmt"]},
					{op: "matches", args: ["@fn", "^(Fprintf|Appendf)$"]},
					{op: "matches", args: ["@fmtstr", #quotedInRaw]},
				]
			}
			diagnose: #diagnose
		}
	}
}
