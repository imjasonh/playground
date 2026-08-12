// ts_array_type_style rewrites the generic-array form `Array<T>` to
// the shorthand `T[]`. Restricted to simple type arguments
// (`type_identifier` / `predefined_type`) so `Array<string | number>`
// is not rewritten to the wrong `string | number[]`.

package ts_array_type_style

import (
	"github.com/imjasonh/pasta/schema"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
	tslang "github.com/imjasonh/pasta/lang/typescript"
)

ts_array_type_style: schema.#Analyzer & {
	name:    "ts_array_type_style"
	version: "0.1.1"
	doc:     "Rewrite Array<T> to T[] for simple T"
	facts: {}

	rules: prefer_shorthand: {
		name: "prefer_shorthand"
		doc:  "Array<T> -> T[]"
		languages: [tslang.Name, tsxlang.Name]
		requires: []
		provides: []

		match: {
			node: "generic_type"
			fields: {
				name: {capture: "outer", pattern: {node: "type_identifier"}}
				type_arguments: {
					capture: "args"
					pattern: {
						node: "type_arguments"
						children: [{
							capture: "inner"
							pattern: {node: ["type_identifier", "predefined_type"]}
						}]
					}
				}
			}
			where: [
				{op: "eq", args: ["@outer", "Array"]},
				{op: "named_child_count", args: ["@args", "1"]},
			]
		}

		diagnose: {
			message:  "Array<T> can be written as T[]"
			severity: "hint"
		}

		rewrite: edits: [{
			target:      "_root"
			replacement: "@inner[]"
		}]
	}
}
