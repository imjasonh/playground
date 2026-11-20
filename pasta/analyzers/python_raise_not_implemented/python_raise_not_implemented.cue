// python_raise_not_implemented flags `raise NotImplemented`.
// NotImplemented is a singleton constant for rich comparison fallbacks,
// not an exception class; raising it throws a TypeError at runtime.
// Use `raise NotImplementedError` instead.

package python_raise_not_implemented

import (
	"github.com/imjasonh/pasta/schema"
	pylang "github.com/imjasonh/pasta/lang/python"
)

python_raise_not_implemented: schema.#Analyzer & {
	name:    "python_raise_not_implemented"
	version: "0.1.0"
	doc:     "Flag `raise NotImplemented` (should be `raise NotImplementedError`)"
	facts: {}

	rules: raise_not_implemented: {
		name:      "raise_not_implemented"
		doc:       "NotImplemented is a constant, not an exception; raising it causes a TypeError"
		languages: [pylang.Name]
		requires: []
		provides: []

		match: {
			node: "raise_statement"
			children: [{
				capture: "exc"
				pattern: {node: "identifier"}
			}]
			where: [
				{op: "eq", args: ["@exc", "NotImplemented"]},
			]
		}

		diagnose: {
			message:  "raise NotImplemented raises TypeError at runtime; use `raise NotImplementedError`"
			severity: "warning"
		}

		rewrite: edits: [{target: "exc", replacement: "NotImplementedError"}]
	}
}
