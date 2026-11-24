// bash_useless_cat flags useless use of `cat` in pipelines (UUOC).
// Piping `cat file | command` creates an unnecessary child process and
// IPC pipe; utilities like grep, head, sed, and awk can read the file
// directly or accept input redirection `< file`.

package bash_useless_cat

import (
	"github.com/imjasonh/pasta/schema"
	bashlang "github.com/imjasonh/pasta/lang/bash"
)

bash_useless_cat: schema.#Analyzer & {
	name:    "bash_useless_cat"
	version: "0.1.0"
	doc:     "Flag useless use of cat in pipelines (UUOC)"
	facts: {}

	rules: useless_cat: {
		name:      "useless_cat"
		doc:       "cat piped into commands creates an unnecessary process and subshell"
		languages: [bashlang.Name]
		requires: []
		provides: []

		match: {
			node: "pipeline"
			children: [
				{
					node: "command"
					fields: {
						name: {capture: "cmd"}
					}
				},
			]
			where: [
				{op: "eq", args: ["@cmd", "cat"]},
			]
		}

		diagnose: {
			message:  "useless use of cat in pipeline; pass the file directly or use input redirection `< file`"
			severity: "warning"
		}
	}
}
