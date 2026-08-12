// js_array_concat_spread flags `[].concat(x)`. Teams often prefer the
// spread form `[...x]`, but that rewrite is *not* equivalent for
// scalars, strings, non-iterables, or `Symbol.isConcatSpreadable`
// objects — so this rule diagnoses only.

package js_array_concat_spread

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
)

js_array_concat_spread: schema.#Analyzer & {
	name:    "js_array_concat_spread"
	version: "0.1.0"
	doc:     "Flag [].concat(x); prefer [...x] when x is known iterable"
	facts: {}

	rules: array_concat_to_spread: {
		name: "array_concat_to_spread"
		doc:  "[].concat(x) can often be [...x]"
		languages: [jslang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: {
				function: {
					node: "member_expression"
					fields: {
						object: {
							capture: "obj"
							pattern: {node: "array"}
						}
						property: {capture: "prop", pattern: {node: "property_identifier"}}
					}
				}
				arguments: {
					capture: "args"
					pattern: {
						node: "arguments"
						children: [{capture: "src"}]
					}
				}
			}
			where: [
				{op: "eq", args: ["@prop", "concat"]},
				// Object must be `[]` empty array literal.
				{op: "empty", args: ["@obj"]},
				// Exactly one argument.
				{op: "named_child_count", args: ["@args", "1"]},
			]
		}

		diagnose: {
			message:  "[].concat(x) can often be written as [...x] when x is iterable"
			severity: "hint"
		}
	}
}
