// java_finalize_overload flags `void finalize(…)` methods that take
// parameters. Those are not overrides of `Object.finalize()`, so they
// look like finalizers but never run. PMD `FinalizeOverloaded` covers
// the same ground. The no-arg override is `java_finalizer`.

package java_finalize_overload

import (
	"github.com/imjasonh/pasta/schema"
	javalang "github.com/imjasonh/pasta/lang/java"
)

java_finalize_overload: schema.#Analyzer & {
	name:    "java_finalize_overload"
	version: "0.1.0"
	doc:     "Flag void finalize(…) overloads that are not Object.finalize"
	facts: {}

	rules: overloaded: {
		name:      "overloaded"
		doc:       "void finalize(args) is not a finalizer"
		languages: [javalang.Name]
		requires: []
		provides: []

		match: {
			node: "method_declaration"
			fields: {
				type: {capture: "ret", pattern: {node: "void_type"}}
				name: {capture: "name"}
				parameters: {
					capture: "params"
					pattern: {node: "formal_parameters"}
				}
			}
			where: [
				{op: "eq", args: ["@name", "finalize"]},
				{op: "not_matches", args: ["@params", "^\\(\\s*\\)$"]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "finalize(…) with parameters is not Object.finalize; rename it so it is not mistaken for a finalizer"
		}
	}
}
