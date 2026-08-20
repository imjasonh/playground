// ruby_double_negation flags `!!x`. The idiom converts to a boolean
// but hides the value and reads as a double negative. RuboCop
// `Style/DoubleNegation` covers the same ground. No auto-fix — the
// replacement (`!x.nil?`, an explicit predicate, …) depends on what
// the author meant.

package ruby_double_negation

import (
	"github.com/imjasonh/pasta/schema"
	rblang "github.com/imjasonh/pasta/lang/ruby"
)

ruby_double_negation: schema.#Analyzer & {
	name:    "ruby_double_negation"
	version: "0.1.0"
	doc:     "Flag !!x boolean conversion"
	facts: {}

	rules: bang_bang: {
		name:      "bang_bang"
		doc:       "!!x is a confusing boolean conversion"
		languages: [rblang.Name]
		requires: []
		provides: []

		match: {
			node: "unary"
			children: [{
				capture: "inner"
				pattern: {node: "unary"}
			}]
			where: [{op: "matches", args: ["@_root", "^!!"]}]
		}

		diagnose: {
			severity: "hint"
			message:  "`!!` converts to boolean via a double negative; prefer an explicit predicate"
		}
	}
}
