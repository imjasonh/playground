// js_no_underscore_dangle flags identifier with a dangling underscore.
// ESLint `no-underscore-dangle` covers the same ground.

package js_no_underscore_dangle

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

js_no_underscore_dangle: schema.#Analyzer & {
	name:    "js_no_underscore_dangle"
	version: "0.1.0"
	doc:     "identifier with a dangling underscore"
	facts: {}
	rules: {
	js_no_underscore_dangle: _base & {
		name: "js_no_underscore_dangle"
		doc:  "identifier with a dangling underscore"
		requires: []
		provides: []
		match: {
			node: "identifier"
			where: [{op: "matches", args: ["@_root", "^_|_$"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "identifier with a dangling underscore"
		}
	}
	}
}
