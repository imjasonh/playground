// js_no_multi_str flags multiline string with a backslash continuation.
// ESLint `no-multi-str` covers the same ground.

package js_no_multi_str

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

js_no_multi_str: schema.#Analyzer & {
	name:    "js_no_multi_str"
	version: "0.1.0"
	doc:     "multiline string with a backslash continuation"
	facts: {}
	rules: {
	js_no_multi_str: _base & {
		name: "js_no_multi_str"
		doc:  "multiline string with a backslash continuation"
		requires: []
		provides: []
		match: {
			node: "string"
			where: [{op: "matches", args: ["@_root", "\\\\\n"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "multiline string with a backslash continuation"
		}
	}
	}
}
