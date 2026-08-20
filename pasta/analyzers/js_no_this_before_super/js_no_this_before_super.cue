// js_no_this_before_super flags this or super property before super() in a subclass constructor.
// ESLint `no-this-before-super` covers the same ground.

package js_no_this_before_super

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

js_no_this_before_super: schema.#Analyzer & {
	name:    "js_no_this_before_super"
	version: "0.1.0"
	doc:     "this or super property before super() in a subclass constructor"
	facts: {}
	rules: {
	js_no_this_before_super: _base & {
		name: "js_no_this_before_super"
		doc:  "this or super property before super() in a subclass constructor"
		requires: []
		provides: []
		match: {
			node: "method_definition"
			fields: {
				name: {capture: "name", pattern: {node: "property_identifier"}}
				body: {
					node: "statement_block"
					adjacent: [
						{
							node: "expression_statement"
							children: [{
								capture: "first"
								pattern: {node: "assignment_expression"}
							}]
						},
						{
							node: "expression_statement"
							children: [{
								node: "call_expression"
								fields: {function: {capture: "fn", pattern: {node: "super"}}}
							}]
						},
					]
				}
			}
			where: [
				{op: "eq", args: ["@name", "constructor"]},
				{op: "matches", args: ["@first", "^this\\b"]},
				{op: "ancestor_is", args: ["@_root", "class_declaration"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "this or super property before super() in a subclass constructor"
		}
	}
	}
}
