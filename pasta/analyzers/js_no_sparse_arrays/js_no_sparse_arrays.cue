// js_no_sparse_arrays flags sparse array literals with holes (`[1,, 2]`
// or `[, 1]`). ESLint `no-sparse-arrays` covers the same ground. A
// trailing comma (`[1, 2,]`) is valid ES5+ and is not a hole.

package js_no_sparse_arrays

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_langs: [jslang.Name, tslang.Name, tsxlang.Name]

_base: {
	languages: _langs
}

js_no_sparse_arrays: schema.#Analyzer & {
	name:    "js_no_sparse_arrays"
	version: "0.1.0"
	doc:     "sparse array literal"
	facts: {}
	rules: {
	js_no_sparse_arrays: _base & {
		name: "js_no_sparse_arrays"
		doc:  "sparse array literal"
		requires: []
		provides: []
		match: {
			node: "array"
			where: [{op: "matches", args: ["@_root", ",\\s*,|\\[\\s*,"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "sparse array literal"
		}
	}
	}
}
