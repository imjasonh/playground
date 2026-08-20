// js_no_lone_blocks flags nested standalone block.
// ESLint `no-lone-blocks` covers the same ground.

package js_no_lone_blocks

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

js_no_lone_blocks: schema.#Analyzer & {
	name:    "js_no_lone_blocks"
	version: "0.1.0"
	doc:     "nested standalone block"
	facts: {}
	rules: {
	js_no_lone_blocks: _base & {
		name: "js_no_lone_blocks"
		doc:  "nested standalone block"
		requires: []
		provides: []
		match: {
			node: "statement_block"
			children: [{capture: "inner", pattern: {node: "statement_block"}}]
			where: [{op: "named_child_count", args: ["@_root", "1"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "nested standalone block"
		}
	}
	}
}
