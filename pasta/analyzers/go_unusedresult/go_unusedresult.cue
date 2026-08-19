// go_unusedresult is a syntactic port of
// golang.org/x/tools/go/analysis/passes/unusedresult.
//
// Calls such as `fmt.Sprintf` and `errors.New` are pure: discarding
// the result is never useful. Pasta flags them when they appear as a
// bare expression statement. Name-only matching cannot distinguish
// similarly named methods on other types.

package go_unusedresult

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

_unusedPkg: {
	_pkg: string
	_fn:  string

	out: {
		languages: [golang.Name]
		requires: []
		provides: []

		match: {
			node: "expression_statement"
			children: [{
				capture: "call"
				pattern: gopat.PackageCall & {
					where: [
						{op: "eq", args: ["@pkg", _pkg]},
						{op: "matches", args: ["@fn", _fn]},
					]
				}
			}]
		}

		diagnose: {
			message:  "result of \(_pkg) call not used"
			severity: "warning"
		}

		rewrite: edits: [{
			target:      "_root"
			replacement: "_ = @call"
		}]
	}
}

go_unusedresult: schema.#Analyzer & {
	name:    "go_unusedresult"
	version: "0.1.0"
	doc:     "Flag unused results of fmt.Sprint*, errors.New, and context.With*"
	facts: {}

	rules: {
		fmt_pure: (_unusedPkg & {
			_pkg: "fmt"
			_fn:  "^(Sprint|Sprintf|Sprintln|Errorf|Append|Appendf|Appendln)$"
		}).out & {
			name: "fmt_pure"
			doc:  "fmt.Sprint* / Errorf / Append* results must be used"
		}
		errors_new: (_unusedPkg & {
			_pkg: "errors"
			_fn:  "^New$"
		}).out & {
			name: "errors_new"
			doc:  "errors.New result must be used"
		}
		context_with: (_unusedPkg & {
			_pkg: "context"
			_fn:  "^With(Cancel|CancelCause|Deadline|DeadlineCause|Timeout|TimeoutCause|Value)$"
		}).out & {
			name: "context_with"
			doc:  "context.With* results must be used"
		}
		slices_pure: (_unusedPkg & {
			_pkg: "slices"
			_fn:  "^(Clone|Clip|Compact|CompactFunc|Delete|DeleteFunc|Grow|Insert|Replace|Repeat|Concat)$"
		}).out & {
			name: "slices_pure"
			doc:  "slices.Clone and similar results must be used"
		}
		sort_reverse: (_unusedPkg & {
			_pkg: "sort"
			_fn:  "^Reverse$"
		}).out & {
			name: "sort_reverse"
			doc:  "sort.Reverse result must be used"
		}
	}
}
