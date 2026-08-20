// go_tests is a syntactic port of
// golang.org/x/tools/go/analysis/passes/tests.
//
// Pasta checks Test/Benchmark/Fuzz functions in `*_test.go` files
// that declare no parameters. The original analyzer also validates
// Example output, TestMain's `*testing.M`, and malformed names such
// as `Testfoo`. The lowercase-suffix case is included; Example
// comments are not.

package go_tests

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

_emptyParams: {
	_kind:  "Test" | "Benchmark" | "Fuzz"
	_param: "*testing.T" | "*testing.B" | "*testing.F"

	out: {
		languages: [golang.Name]
		requires: []
		provides: []
		file_match: ["*_test.go"]

		match: {
			node: "function_declaration"
			fields: {
				name:       {capture: "name"}
				parameters: {capture: "params"}
			}
			where: [
				{op: "matches", args: ["@name", "^\(_kind)"]},
				{op: "not_matches", args: ["@name", "^TestMain$"]},
				{op: "named_child_count", args: ["@params", "0"]},
			]
		}

		diagnose: {
			message:  "wrong signature for \(_kind) function, must have parameter \(_param)"
			severity: "warning"
		}
	}
}

go_tests: schema.#Analyzer & {
	name:    "go_tests"
	version: "0.1.0"
	doc:     "Flag Test/Benchmark/Fuzz functions with no testing parameter"
	facts: {}

	rules: {
		test_no_param: (_emptyParams & {_kind: "Test", _param: "*testing.T"}).out & {
			name: "test_no_param"
			doc:  "TestXxx must take *testing.T"
		}
		bench_no_param: (_emptyParams & {_kind: "Benchmark", _param: "*testing.B"}).out & {
			name: "bench_no_param"
			doc:  "BenchmarkXxx must take *testing.B"
		}
		fuzz_no_param: (_emptyParams & {_kind: "Fuzz", _param: "*testing.F"}).out & {
			name: "fuzz_no_param"
			doc:  "FuzzXxx must take *testing.F"
		}
		malformed_name: {
			name: "malformed_name"
			doc:  "Testfoo is not a test; the next letter must be uppercase"
			languages: [golang.Name]
			requires: []
			provides: []
			file_match: ["*_test.go"]

			match: {
				node: "function_declaration"
				fields: name: {capture: "name"}
				where: [{op: "matches", args: ["@name", "^(Test|Benchmark|Fuzz)[a-z]"]}]
			}

			diagnose: {
				message:  "@name has a malformed name: next letter after Test/Benchmark/Fuzz must be uppercase"
				severity: "warning"
			}
		}
	}
}
