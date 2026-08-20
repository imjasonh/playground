// ts_inferrable_types drops trivial type annotations that TypeScript
// already infers from a literal initializer:
//
//   const a: string = "a"   ->   const a = "a"
//   const n: number = 1     ->   const n = 1
//   const b: boolean = true ->   const b = true
//
// `@typescript-eslint/no-inferrable-types` covers the same ground.
// Restricted to `string` / `number` / `boolean` literals so
// `const n: number = f()` and `let n: number` stay annotated.

package ts_inferrable_types

import (
	"github.com/imjasonh/pasta/schema"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
	tslang "github.com/imjasonh/pasta/lang/typescript"
)

_langs: [tslang.Name, tsxlang.Name]

_inferrable: {
	_name:     string
	_node:     string
	_ty:       "string" | "number" | "boolean"
	_initNode: string | [...string]

	out: {
		name:      _name
		doc:       "drop inferrable `\(_ty)` annotation"
		languages: _langs
		requires: []
		provides: []

		match: {
			node: _node
			fields: {
				type: {
					capture: "ann"
					pattern: {
						node: "type_annotation"
						children: [{
							capture: "ty"
							pattern: {node: "predefined_type"}
						}]
					}
				}
				value: {
					capture: "init"
					pattern: {node: _initNode}
				}
			}
			where: [{op: "eq", args: ["@ty", _ty]}]
		}

		diagnose: {
			severity: "hint"
			message:  "type `\(_ty)` is inferrable from the literal; drop the annotation"
		}

		rewrite: edits: [{
			target:      "ann"
			replacement: ""
		}]
	}
}

ts_inferrable_types: schema.#Analyzer & {
	name:    "ts_inferrable_types"
	version: "0.1.0"
	doc:     "Drop `: string` / `: number` / `: boolean` when the initializer is a matching literal"
	facts: {}

	rules: {
		var_string: (_inferrable & {
			_name:     "var_string"
			_node:     "variable_declarator"
			_ty:       "string"
			_initNode: "string"
		}).out

		var_number: (_inferrable & {
			_name:     "var_number"
			_node:     "variable_declarator"
			_ty:       "number"
			_initNode: "number"
		}).out

		var_boolean: (_inferrable & {
			_name:     "var_boolean"
			_node:     "variable_declarator"
			_ty:       "boolean"
			_initNode: ["true", "false"]
		}).out

		param_string: (_inferrable & {
			_name:     "param_string"
			_node:     "required_parameter"
			_ty:       "string"
			_initNode: "string"
		}).out

		param_number: (_inferrable & {
			_name:     "param_number"
			_node:     "required_parameter"
			_ty:       "number"
			_initNode: "number"
		}).out

		param_boolean: (_inferrable & {
			_name:     "param_boolean"
			_node:     "required_parameter"
			_ty:       "boolean"
			_initNode: ["true", "false"]
		}).out
	}
}
