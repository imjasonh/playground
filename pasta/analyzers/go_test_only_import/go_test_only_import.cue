// go_test_only_import flags an import of a package meant only for test
// code, from a file that isn't itself a _test.go file.
//
// Go has no built-in way to restrict a package's import to test files:
// unlike a package under internal/, which the compiler really does reject
// outside its module subtree, "importable only from *_test.go" isn't a
// visibility rule the toolchain enforces. This rule is the next best
// thing, enforced by the pre-commit hook and the pasta leg of CI, both
// already required. The playground root's .pasta/pasta.cue exempts
// *_test.go files from this rule with disabled_on, so it only fires on
// the non-test files the package is actually meant to exclude.
//
// Today that's testtrace: its automatic span-binding walks the call
// stack on most span starts, which is overhead a production binary
// shouldn't pay and a signal a production binary has no running test to
// find anyway. Add another eq predicate to extend this to a future
// package that earns the same treatment.

package go_test_only_import

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_test_only_import: schema.#Analyzer & {
	name:    "go_test_only_import"
	version: "0.1.0"
	doc:     "Flag an import of a test-only package from a non-test file"

	facts: {}

	rules: testtrace: {
		name: "testtrace"
		doc:  "testtrace imported outside a _test.go file"
		languages: [golang.Name]
		requires: []
		provides: []

		require_substring: ["testtrace"]

		match: {
			node: "import_spec"
			fields: path: {capture: "path", pattern: {node: "interpreted_string_literal"}}
			where: [
				{op: "eq", args: ["@path", "\"github.com/imjasonh/playground/testtrace\""]},
			]
		}

		diagnose: {
			message:  "testtrace instruments tests; import it only from a _test.go file"
			severity: "warning"
		}
	}
}
