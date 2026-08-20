// js_no_control_regex flags ASCII control-character escapes in a
// regular expression (`\x00`, `\u0001`, `\cA`). ESLint
// `no-control-regex` covers the same ground. Common whitespace
// escapes (`\n`, `\t`, `\r`) are not hex/unicode control forms and
// are left alone. A regex that uses NUL as a sentinel needs
// `pasta:ignore` on that line.

package js_no_control_regex

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_langs: [jslang.Name, tslang.Name, tsxlang.Name]

_base: {
	languages: _langs
}

js_no_control_regex: schema.#Analyzer & {
	name:    "js_no_control_regex"
	version: "0.1.0"
	doc:     "control character in a regular expression"
	facts: {}
	rules: {
		js_no_control_regex: _base & {
			name: "js_no_control_regex"
			doc:  "control character in a regular expression"
			requires: []
			provides: []
			match: {
				node: "regex_pattern"
				where: [{
					op: "matches"
					args: ["@_root", "\\\\x[01][0-9a-fA-F]|\\\\u00[01][0-9a-fA-F]|\\\\c[A-Z]"]
				}]
			}
			diagnose: {
				severity: "warning"
				message:  "control character in a regular expression"
			}
		}
	}
}
