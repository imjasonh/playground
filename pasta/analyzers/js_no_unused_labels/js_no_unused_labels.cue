// js_no_unused_labels flags labeled statement whose body has no matching break/continue.
// ESLint `no-unused-labels` covers the same ground.

package js_no_unused_labels

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

js_no_unused_labels: schema.#Analyzer & {
	name:    "js_no_unused_labels"
	version: "0.1.0"
	doc:     "labeled statement whose body has no matching break/continue"
	facts: {}
	rules: {
	js_no_unused_labels: _base & {
		name: "js_no_unused_labels"
		doc:  "labeled statement whose body has no matching break/continue"
		requires: []
		provides: []
		match: {
			node: "labeled_statement"
			fields: {
				label: {capture: "lab", pattern: {node: "statement_identifier"}}
				body: {capture: "body"}
			}
			where: [{op: "not_matches", args: ["@body", "\\b(break|continue)\\s+"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "labeled statement whose body has no matching break/continue"
		}
	}
	}
}
