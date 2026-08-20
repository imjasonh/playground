// js_no_class_assign flags assignment to a class name.
// ESLint `no-class-assign` covers the same ground.

package js_no_class_assign

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

js_no_class_assign: schema.#Analyzer & {
	name:    "js_no_class_assign"
	version: "0.1.0"
	doc:     "assignment to a class name"
	facts: {
		class_name: {kind: "class_name"}
	}
	rules: {

	mark_class_name: _base & {
		name: "mark_class_name"
		doc:  "Record class declaration names"
		requires: []
		provides: ["class_name"]
		match: {
			node: "class_declaration"
			fields: {
				name: {capture: "name", pattern: {node: "identifier"}}
			}
		}
		emit: [{fact: "class_name", attach: "name"}]
	}
	js_no_class_assign: _base & {
		name: "js_no_class_assign"
		doc:  "assignment to a class name"
		requires: ["class_name"]
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs", pattern: {node: "identifier"}}
			}
			where: [{op: "has_fact", args: ["@lhs", "class_name"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "assignment to a class name"
		}
	}
	}
}
