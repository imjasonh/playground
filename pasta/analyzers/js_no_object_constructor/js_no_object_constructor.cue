// js_no_object_constructor flags Object() / new Object() with no arguments.
// ESLint `no-object-constructor` covers the same ground.

package js_no_object_constructor

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

js_no_object_constructor: schema.#Analyzer & {
	name:    "js_no_object_constructor"
	version: "0.1.0"
	doc:     "Object() / new Object() with no arguments"
	facts: {}
	rules: {
	js_no_object_constructor: _base & {
		name: "js_no_object_constructor"
		doc:  "Object() / new Object() with no arguments"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor", pattern: {node: "identifier"}}
				arguments: {capture: "args", pattern: {node: "arguments"}}
			}
			where: [
				{op: "eq", args: ["@ctor", "Object"]},
				{op: "empty", args: ["@args"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "Object() / new Object() with no arguments"
		}
	}
	js_no_object_constructor_call: _base & {
		name: "js_no_object_constructor_call"
		doc:  "Object() call with no arguments"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {capture: "args", pattern: {node: "arguments"}}
			}
			where: [
				{op: "eq", args: ["@fn", "Object"]},
				{op: "empty", args: ["@args"]},
			]
		}
		diagnose: {
			severity: "hint"
			message:  "Object() call with no arguments"
		}
	}
	}
}
