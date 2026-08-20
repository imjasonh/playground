// bash_unquoted_expansion flags `[ -z $THING ]` / `[ -n $FOO ]` and
// other unary `test` operators whose operand is an unquoted `$VAR`
// expansion. When the variable is empty or contains whitespace, the
// test is a syntax error or splits into extra arguments. ShellCheck
// SC2086 covers the same ground. Quoted `"$THING"` is left alone.
// No auto-fix — adding quotes is usually right, but some callers rely
// on word-splitting.
//
// Named `bash_unquoted_expansion` rather than `bash_unquoted_test`
// because CUE skips files matching `*_test.cue` outside test mode.

package bash_unquoted_expansion

import (
	"github.com/imjasonh/pasta/schema"
	bashlang "github.com/imjasonh/pasta/lang/bash"
)

bash_unquoted_expansion: schema.#Analyzer & {
	name:    "bash_unquoted_expansion"
	version: "0.1.0"
	doc:     "Flag unquoted $VAR in [ -z $VAR ] tests"
	facts: {}

	rules: unquoted_unary: {
		name:      "unquoted_unary"
		doc:       "[ -z $THING ] splits when THING is empty or has spaces"
		languages: [bashlang.Name]
		requires: []
		provides: []

		match: {
			node: "unary_expression"
			children: [
				{node: "test_operator"},
				{
					capture: "arg"
					pattern: {node: "simple_expansion"}
				},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "unquoted $VAR in [ ] test; quote it so empty or spaced values stay one argument"
		}
	}
}
