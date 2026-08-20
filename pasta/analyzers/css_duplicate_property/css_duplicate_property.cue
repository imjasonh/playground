// css_duplicate_property flags consecutive declarations of the same
// property in one block (`color: pink; color: red;`). The later
// declaration wins; the earlier one is dead. Stylelint
// `declaration-block-no-duplicate-properties` covers the same ground
// and also catches non-consecutive duplicates; this rule only sees
// adjacent pairs (pasta has no unordered sibling search yet).
// No auto-fix — which declaration to keep is a product choice.
//
// Disable in playground `.pasta/pasta.cue` if a tree uses
// `min-height: 100vh` then `min-height: 100dvh` as a browser fallback.

package css_duplicate_property

import (
	"github.com/imjasonh/pasta/schema"
	csslang "github.com/imjasonh/pasta/lang/css"
)

css_duplicate_property: schema.#Analyzer & {
	name:    "css_duplicate_property"
	version: "0.1.0"
	doc:     "Flag consecutive duplicate CSS properties in a block"
	facts: {}

	rules: consecutive_dup: {
		name:      "consecutive_dup"
		doc:       "Two adjacent declarations with the same property name"
		languages: [csslang.Name]
		requires: []
		provides: []

		match: {
			node: "block"
			adjacent: [
				{
					capture: "first"
					pattern: {
						node: "declaration"
						children: [{
							capture: "p1"
							pattern: {node: "property_name"}
						}]
					}
				},
				{
					capture: "second"
					pattern: {
						node: "declaration"
						children: [{
							capture: "p2"
							pattern: {node: "property_name"}
						}]
					}
				},
			]
			where: [{op: "same_ident", args: ["@p1", "@p2"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "duplicate property `@p1`; the later declaration wins"
		}
	}
}
