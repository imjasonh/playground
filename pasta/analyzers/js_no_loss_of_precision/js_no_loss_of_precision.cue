// js_no_loss_of_precision flags numeric literal is too large to be represented precisely.
// ESLint `no-loss-of-precision` covers the same ground.

package js_no_loss_of_precision

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

js_no_loss_of_precision: schema.#Analyzer & {
	name:    "js_no_loss_of_precision"
	version: "0.1.0"
	doc:     "numeric literal is too large to be represented precisely"
	facts: {}
	rules: {
	js_no_loss_of_precision: _base & {
		name: "js_no_loss_of_precision"
		doc:  "numeric literal is too large to be represented precisely"
		requires: []
		provides: []
		match: {
			node: "number"
			where: [{op: "matches", args: ["@_root", "^[0-9]{17,}$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "numeric literal is too large to be represented precisely"
		}
	}
	}
}
