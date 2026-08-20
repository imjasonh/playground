// js_no_inner_declarations flags function declaration in a nested block.
// ESLint `no-inner-declarations` covers the same ground.

package js_no_inner_declarations

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

js_no_inner_declarations: schema.#Analyzer & {
	name:    "js_no_inner_declarations"
	version: "0.1.0"
	doc:     "function declaration in a nested block"
	facts: {}
	rules: {
	js_no_inner_declarations: _base & {
		name: "js_no_inner_declarations"
		doc:  "function declaration in a nested block"
		requires: []
		provides: []
		match: {
			node: "function_declaration"
			where: [{
				op: "ancestor_is"
				args: ["@_root", ["if_statement", "for_statement", "for_in_statement", "while_statement", "do_statement", "switch_case", "switch_default"]]
			}]
		}
		diagnose: {
			severity: "warning"
			message:  "function declaration in a nested block"
		}
	}
	}
}
