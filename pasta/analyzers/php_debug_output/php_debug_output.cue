// php_debug_output flags committed debugging helpers (`var_dump`,
// `print_r`, `debug_zval_dump`). These dump values to the response /
// stdout and almost never belong in production code.

package php_debug_output

import (
	"github.com/imjasonh/pasta/schema"
	phplang "github.com/imjasonh/pasta/lang/php"
)

php_debug_output: schema.#Analyzer & {
	name:    "php_debug_output"
	version: "0.1.0"
	doc:     "Flag var_dump / print_r / debug_zval_dump"
	facts: {}

	rules: debug_call: {
		name:      "debug_call"
		doc:       "Debug dump functions should not be committed"
		languages: [phplang.Name]
		requires: []
		provides: []

		match: {
			node: "function_call_expression"
			children: [{
				capture: "fn"
				pattern: {node: "name"}
			}]
			where: [{op: "matches", args: ["@fn", "^(var_dump|print_r|debug_zval_dump)$"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "debug output should not be committed"
		}
	}
}
