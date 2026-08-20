// disabled_on exercises project-config path globs: two rules fire on
// most files, but `dropped` is skipped on skip_me.py.

package disabled_on

import (
	"github.com/imjasonh/pasta/schema"
	pylang "github.com/imjasonh/pasta/lang/python"
)

_printRule: {
	_msg: string
	out: {
		languages: [pylang.Name]
		requires: []
		provides: []
		match: {
			node: "call"
			fields: function: {capture: "fn"}
			where: [{op: "token_eq", args: ["@fn", "print"]}]
		}
		diagnose: message: _msg
	}
}

disabled_on: schema.#Analyzer & {
	name:    "disabled_on"
	version: "0.1.0"
	doc:     "Demo of pasta.cue disabled_on path globs"
	facts: {}

	rules: {
		kept: (_printRule & {_msg: "kept rule fired"}).out & {
			name: "kept"
			doc:  "stays enabled on every file"
		}
		dropped: (_printRule & {_msg: "dropped rule fired"}).out & {
			name: "dropped"
			doc:  "disabled on skip_me.py by pasta.cue"
		}
	}
}
