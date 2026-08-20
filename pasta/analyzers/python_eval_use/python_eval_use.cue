// python_eval_use flags `eval(...)` calls. `eval` executes its
// argument as Python, which is a code-injection hazard whenever any
// argument is influenced by user input or external data. Bandit B307
// covers the same ground. `foo.eval()` attribute calls are left
// alone. No auto-fix — the right replacement (ast.literal_eval,
// a lookup table, …) is per-call-site.

package python_eval_use

import (
	"github.com/imjasonh/pasta/schema"
	pylang "github.com/imjasonh/pasta/lang/python"
)

python_eval_use: schema.#Analyzer & {
	name:    "python_eval_use"
	version: "0.1.0"
	doc:     "Flag eval() — code-injection hazard"
	facts: {}

	rules: eval_call: {
		name: "eval_call"
		doc:  "eval() executes a string as Python"
		languages: [pylang.Name]
		requires: []
		provides: []

		match: {
			node: "call"
			fields: {
				function: {
					capture: "fn"
					pattern: {node: "identifier"}
				}
			}
			where: [{op: "eq", args: ["@fn", "eval"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "eval() executes its argument as Python — code-injection hazard"
		}
	}
}
