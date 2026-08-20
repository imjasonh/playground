// bash_grep_glob flags `grep '*foo*'` — a quoted pattern that looks
// like a glob. grep treats `*` as a regex quantifier, not a glob, so
// the call either errors or matches the wrong thing. ShellCheck SC2063
// covers the same ground. Restricted to grep's first argument so
// `grep foo '*.txt'` (globbed filenames) is left alone. No auto-fix.

package bash_grep_glob

import (
	"github.com/imjasonh/pasta/schema"
	bashlang "github.com/imjasonh/pasta/lang/bash"
)

bash_grep_glob: schema.#Analyzer & {
	name:    "bash_grep_glob"
	version: "0.1.0"
	doc:     "Flag grep patterns that look like globs"
	facts: {}

	rules: glob_pattern: {
		name: "glob_pattern"
		doc:  "grep '*foo*' — * is regex, not glob"
		languages: [bashlang.Name]
		requires: []
		provides: []

		match: {
			node: "command"
			fields: {
				name: {capture: "cmd"}
			}
			children: [
				{node: "command_name"},
				{
					capture: "pat"
					pattern: {node: ["raw_string", "string"]}
				},
			]
			where: [
				{op: "eq", args: ["@cmd", "grep"]},
				{op: "matches", args: ["@pat", "\\*"]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "grep pattern looks like a glob; grep uses regex, so write a regex or use find"
		}
	}
}
