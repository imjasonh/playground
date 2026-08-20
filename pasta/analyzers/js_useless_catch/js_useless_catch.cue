// js_useless_catch flags `catch (e) { throw e; }` — a catch clause
// whose only statement rethrows the bound identifier. The catch does
// nothing and the extra frame obscures the original stack. ESLint
// `no-useless-catch` covers the same ground.
//
// Catches that log, wrap, or throw a different value are left alone.
// Optional `catch { throw e }` (no binding) is not this pattern.
// No auto-fix: dropping the try/catch needs the try body in hand,
// and comments inside the catch would be lost.

package js_useless_catch

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
	tslang "github.com/imjasonh/pasta/lang/typescript"
)

js_useless_catch: schema.#Analyzer & {
	name:    "js_useless_catch"
	version: "0.1.0"
	doc:     "Flag catch clauses that only rethrow the bound error"
	facts: {}

	rules: rethrow_only: {
		name: "rethrow_only"
		doc:  "catch (e) { throw e; } is a no-op wrapper"
		languages: [jslang.Name, tslang.Name, tsxlang.Name]
		requires: []
		provides: []

		match: {
			node: "catch_clause"
			fields: {
				parameter: {
					capture: "param"
					pattern: {node: "identifier"}
				}
				body: {
					capture: "body"
					pattern: {
						node: "statement_block"
						children: [{
							node: "throw_statement"
							children: [{
								capture: "thrown"
								pattern: {node: "identifier"}
							}]
						}]
					}
				}
			}
			where: [
				{op: "same_ident", args: ["@param", "@thrown"]},
				{op: "named_child_count", args: ["@body", "1"]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "catch clause only rethrows the bound error; remove the try/catch"
		}
	}
}
