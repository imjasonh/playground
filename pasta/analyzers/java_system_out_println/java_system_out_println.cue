// java_system_out_println flags `System.out` / `System.err` print
// calls. Production code should use a logger; stdout/stderr dumps are
// hard to redirect, filter, or correlate in services.

package java_system_out_println

import (
	"github.com/imjasonh/pasta/schema"
	javalang "github.com/imjasonh/pasta/lang/java"
)

java_system_out_println: schema.#Analyzer & {
	name:    "java_system_out_println"
	version: "0.1.0"
	doc:     "Flag System.out/err.print* — prefer a logger"
	facts: {}

	rules: system_print: {
		name:      "system_print"
		doc:       "System.out/err.print*"
		languages: [javalang.Name]
		requires: []
		provides: []

		match: {
			node: "method_invocation"
			fields: {
				object: {capture: "obj"}
				name: {
					capture: "method"
					pattern: {node: "identifier"}
				}
			}
			where: [
				{op: "matches", args: ["@obj", "^System\\.(out|err)$"]},
				{op: "matches", args: ["@method", "^(print|println|printf)$"]},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "use a logger instead of System.out/err"
		}
	}
}
