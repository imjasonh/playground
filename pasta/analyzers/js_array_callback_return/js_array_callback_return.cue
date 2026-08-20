// js_array_callback_return flags array callback with a block body and no return.
// ESLint `array-callback-return` covers the same ground.

package js_array_callback_return

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

js_array_callback_return: schema.#Analyzer & {
	name:    "js_array_callback_return"
	version: "0.1.0"
	doc:     "array callback with a block body and no return"
	facts: {}
	rules: {
	js_array_callback_return: _base & {
		name: "js_array_callback_return"
		doc:  "array callback with a block body and no return"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
				arguments: {
					node: "arguments"
					children: [{
						capture: "cb"
						pattern: {
							node: ["arrow_function", "function_expression"]
							fields: {
								body: {capture: "body", pattern: {node: "statement_block"}}
							}
						}
					}]
				}
			}
			where: [
				{op: "matches", args: ["@prop", "^(map|filter|every|some|find|findIndex|findLast|findLastIndex|reduce|reduceRight|flatMap|from)$"]},
				{op: "subtree_lacks", args: ["@body", "return_statement"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "array callback with a block body and no return"
		}
	}
	}
}
