// js_new_parens flags `new Foo` without parentheses.
//
// Google JavaScript style: never invoke a constructor in a `new`
// expression without `()`. `new Foo()` and `new Foo.Bar()` have an
// arguments list. `new Foo` does not.
// https://google.github.io/styleguide/jsguide.html#disallowed-features-omitting-parents-with-new

package js_new_parens

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

js_new_parens: schema.#Analyzer & {
	name:    "js_new_parens"
	version: "0.1.0"
	doc:     "Flag new Foo without parentheses"
	facts: {}

	rules: js_new_parens: {
		name:      "js_new_parens"
		doc:       "constructor call omits ()"
		languages: [jslang.Name, tslang.Name, tsxlang.Name]
		requires: []
		provides: []

		match: {
			node:          "new_expression"
			absent_fields: ["arguments"]
		}

		diagnose: {
			message:  "constructor call omits (); write new Foo()"
			severity: "warning"
		}
	}
}
