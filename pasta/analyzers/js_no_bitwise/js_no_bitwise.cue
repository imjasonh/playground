// js_no_bitwise flags bitwise operator.
// ESLint `no-bitwise` covers the same ground.

package js_no_bitwise

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

js_no_bitwise: schema.#Analyzer & {
	name:    "js_no_bitwise"
	version: "0.1.0"
	doc:     "bitwise operator"
	facts: {}
	rules: {
	js_no_bitwise: _base & {
		name: "js_no_bitwise"
		doc:  "bitwise operator"
		requires: []
		provides: []
		match: {
			node: "binary_expression"
			fields: {
				operator: {capture: "op"}
			}
			where: [{op: "matches", args: ["@op", "^(&|\\||\\^|<<|>>|>>>)$"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "bitwise operator"
		}
	}
	js_no_bitwise_not: _base & {
		name: "js_no_bitwise_not"
		doc:  "bitwise not"
		requires: []
		provides: []
		match: {
			node: "unary_expression"
			fields: {
				operator: {capture: "op"}
			}
			where: [{op: "token_eq", args: ["@op", "~"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "bitwise not"
		}
	}
	}
}
