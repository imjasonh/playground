// c_unchecked_stdlib flags C library calls that are easy to misuse:
// `system`, unbounded string copies (`strcpy` / `strcat` / `sprintf`),
// and the `ato*` family (no error reporting). clang-tidy's
// `clang-analyzer-security.insecureAPI.*` and `cert-*` checks cover
// the same ground. `gets` is `c_gets_unsafe`. No auto-fix — the
// bounded replacement (`strncpy`, `strtol`, `execve`, …) depends on
// the call.

package c_unchecked_stdlib

import (
	"github.com/imjasonh/pasta/schema"
	clang "github.com/imjasonh/pasta/lang/c"
	cpplang "github.com/imjasonh/pasta/lang/cpp"
)

c_unchecked_stdlib: schema.#Analyzer & {
	name:    "c_unchecked_stdlib"
	version: "0.1.0"
	doc:     "Flag system/strcpy/strcat/sprintf/ato* — easy to misuse"
	facts: {}

	rules: insecure_call: {
		name: "insecure_call"
		doc:  "Flag system, unbounded string copy, and ato* conversions"
		languages: [clang.Name, cpplang.Name]
		requires: []
		provides: []

		match: {
			node: "call_expression"
			fields: function: {
				capture: "fn"
				pattern: {node: "identifier"}
			}
			where: [{op: "matches", args: ["@fn", "^(system|strcpy|strcat|sprintf|atoi|atol|atoll|atof)$"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "`@fn` is easy to misuse; prefer a bounded or error-reporting alternative"
		}
	}
}
