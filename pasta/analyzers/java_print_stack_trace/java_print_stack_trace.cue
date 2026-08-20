// java_print_stack_trace flags `e.printStackTrace()`. The call dumps
// a stack to stderr with no correlation id, and it is easy to leave in
// production. SpotBugs flags the same call. Prefer a logger.
// No auto-fix.

package java_print_stack_trace

import (
	"github.com/imjasonh/pasta/schema"
	javalang "github.com/imjasonh/pasta/lang/java"
)

java_print_stack_trace: schema.#Analyzer & {
	name:    "java_print_stack_trace"
	version: "0.1.0"
	doc:     "Flag e.printStackTrace() — prefer a logger"
	facts: {}

	rules: print_stack: {
		name:      "print_stack"
		doc:       "e.printStackTrace(…)"
		languages: [javalang.Name]
		requires: []
		provides: []

		match: {
			node: "method_invocation"
			fields: {
				name: {
					capture: "method"
					pattern: {node: "identifier"}
				}
			}
			where: [{op: "eq", args: ["@method", "printStackTrace"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "printStackTrace dumps to stderr; use a logger"
		}
	}
}
