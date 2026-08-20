// js_prefer_regex_literals flags RegExp constructor with a string literal.
// ESLint `prefer-regex-literals` covers the same ground.

package js_prefer_regex_literals

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

js_prefer_regex_literals: schema.#Analyzer & {
	name:    "js_prefer_regex_literals"
	version: "0.1.0"
	doc:     "RegExp constructor with a string literal"
	facts: {}
	rules: {
	js_prefer_regex_literals: _base & {
		name: "js_prefer_regex_literals"
		doc:  "RegExp constructor with a string literal"
		requires: []
		provides: []
		match: {
			node: "new_expression"
			fields: {
				constructor: {capture: "ctor", pattern: {node: "identifier"}}
				arguments: {
					node: "arguments"
					children: [{node: "string"}]
				}
			}
			where: [{op: "eq", args: ["@ctor", "RegExp"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "RegExp constructor with a string literal"
		}
	}
	js_prefer_regex_literals_call: _base & {
		name: "js_prefer_regex_literals_call"
		doc:  "RegExp() call with a string literal"
		requires: []
		provides: []
		match: {
			node: "call_expression"
			fields: {
				function: {capture: "fn", pattern: {node: "identifier"}}
				arguments: {
					node: "arguments"
					children: [{node: "string"}]
				}
			}
			where: [{op: "eq", args: ["@fn", "RegExp"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "RegExp() call with a string literal"
		}
	}
	}
}
