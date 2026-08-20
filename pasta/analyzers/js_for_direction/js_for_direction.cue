// js_for_direction flags for-loop update moves the counter the wrong way.
// ESLint `for-direction` covers the same ground.

package js_for_direction

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

js_for_direction: schema.#Analyzer & {
	name:    "js_for_direction"
	version: "0.1.0"
	doc:     "for-loop update moves the counter the wrong way"
	facts: {}
	rules: {
	js_for_direction: _base & {
		name: "js_for_direction"
		doc:  "for-loop update moves the counter the wrong way"
		requires: []
		provides: []
		match: {
			node: "for_statement"
			fields: {
				condition: {capture: "cond"}
				increment: {capture: "inc"}
			}
			where: [
				{op: "matches", args: ["@cond", "<"]},
				{op: "matches", args: ["@inc", "--"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "for-loop update moves the counter the wrong way"
		}
	}
	js_for_direction_up: _base & {
		name: "js_for_direction_up"
		doc:  "for-loop ++ with a > test moves the wrong way"
		requires: []
		provides: []
		match: {
			node: "for_statement"
			fields: {
				condition: {capture: "cond"}
				increment: {capture: "inc"}
			}
			where: [
				{op: "matches", args: ["@cond", ">"]},
				{op: "matches", args: ["@inc", "\\+\\+"]},
			]
		}
		diagnose: {
			severity: "warning"
			message:  "for-loop ++ with a > test moves the wrong way"
		}
	}
	}
}
