// js_default_case flags switch without a default clause.
// ESLint `default-case` covers the same ground.

package js_default_case

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

js_default_case: schema.#Analyzer & {
	name:    "js_default_case"
	version: "0.1.0"
	doc:     "switch without a default clause"
	facts: {}
	rules: {
	js_default_case: _base & {
		name: "js_default_case"
		doc:  "switch without a default clause"
		requires: []
		provides: []
		match: {
			node: "switch_body"
			where: [{op: "subtree_lacks", args: ["@_root", "switch_default"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "switch without a default clause"
		}
	}
	}
}
