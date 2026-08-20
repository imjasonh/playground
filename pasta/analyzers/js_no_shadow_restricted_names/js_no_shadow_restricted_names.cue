// js_no_shadow_restricted_names flags binding named undefined/NaN/Infinity/arguments/eval.
// ESLint `no-shadow-restricted-names` covers the same ground.

package js_no_shadow_restricted_names

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

js_no_shadow_restricted_names: schema.#Analyzer & {
	name:    "js_no_shadow_restricted_names"
	version: "0.1.0"
	doc:     "binding named undefined/NaN/Infinity/arguments/eval"
	facts: {}
	rules: {
	js_no_shadow_restricted_names: _base & {
		name: "js_no_shadow_restricted_names"
		doc:  "binding named undefined/NaN/Infinity/arguments/eval"
		requires: []
		provides: []
		match: {
			node: ["function_declaration", "function_expression", "generator_function_declaration"]
			fields: {
				name: {capture: "name", pattern: {node: "identifier"}}
			}
			where: [{op: "matches", args: ["@name", "^(undefined|NaN|Infinity|arguments|eval)$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "binding named undefined/NaN/Infinity/arguments/eval"
		}
	}
	js_no_shadow_restricted_let: _base & {
		name: "js_no_shadow_restricted_let"
		doc:  "let/const/var named undefined/NaN/Infinity/arguments/eval"
		requires: []
		provides: []
		match: {
			node: "variable_declarator"
			fields: {
				name: {capture: "name", pattern: {node: "identifier"}}
			}
			where: [{op: "matches", args: ["@name", "^(undefined|NaN|Infinity|arguments|eval)$"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "let/const/var named undefined/NaN/Infinity/arguments/eval"
		}
	}
	}
}
