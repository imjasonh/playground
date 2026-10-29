// go_error_punctuation flags errors.New and fmt.Errorf literals that
// end in `.`, `!`, or `?`.
//
// Google Go style: error strings should not end with punctuation,
// because they are usually wrapped in other context before display.
// A trailing `...` is a usage ellipsis, not sentence punctuation, and
// is left alone. Capitalization is not checked here: the guide allows
// an error to start with an exported name, a proper noun, or an
// acronym, and syntax cannot tell those apart.
// https://google.github.io/styleguide/go/decisions#error-strings

package go_error_punctuation

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

// The last non-ellipsis punctuation, then the closing quote. `...`
// fails because the character before the final dot is itself a dot.
#endsWithPunct: #"(?s).*[^.!?][.!?]("|`)$"#

go_error_punctuation: schema.#Analyzer & {
	name:    "go_error_punctuation"
	version: "0.1.0"
	doc:     "Flag errors.New and fmt.Errorf literals that end with punctuation"
	facts: {}

	rules: {
		errors_new: {
			name:      "go_error_punctuation"
			doc:       "errors.New literal ends with punctuation"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [{
						capture: "msg"
						pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}
					}]
				}
				where: [
					{op: "eq", args: ["@pkg", "errors"]},
					{op: "eq", args: ["@fn", "New"]},
					{op: "matches", args: ["@msg", #endsWithPunct]},
				]
			}

			diagnose: {
				message:  "error string ends with punctuation"
				severity: "warning"
			}
		}

		fmt_errorf: {
			name:      "go_error_punctuation"
			doc:       "fmt.Errorf format string ends with punctuation"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [{
						capture: "msg"
						pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}
					}]
				}
				where: [
					{op: "eq", args: ["@pkg", "fmt"]},
					{op: "eq", args: ["@fn", "Errorf"]},
					{op: "matches", args: ["@msg", #endsWithPunct]},
				]
			}

			diagnose: {
				message:  "error string ends with punctuation"
				severity: "warning"
			}
		}
	}
}
