// js_no_script_url flags javascript: URL.
// ESLint `no-script-url` covers the same ground.

package js_no_script_url

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

js_no_script_url: schema.#Analyzer & {
	name:    "js_no_script_url"
	version: "0.1.0"
	doc:     "javascript: URL"
	facts: {}
	rules: {
	js_no_script_url: _base & {
		name: "js_no_script_url"
		doc:  "javascript: URL"
		requires: []
		provides: []
		match: {
			node: "string"
			where: [{op: "matches", args: ["@_root", "^['\"]javascript:"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "javascript: URL"
		}
	}
	}
}
