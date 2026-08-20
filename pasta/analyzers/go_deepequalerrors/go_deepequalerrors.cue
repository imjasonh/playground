// go_deepequalerrors is a syntactic port of
// golang.org/x/tools/go/analysis/passes/deepequalerrors.
//
// `reflect.DeepEqual` on `error` values compares pointers in the
// interface, not `Error()` strings. Pasta flags `DeepEqual` when an
// argument is `errors.New(...)` or `fmt.Errorf(...)`. It cannot see
// typed variables of interface type `error`. Inner constructor
// captures use distinct names so they do not overwrite `@pkg`/`@fn`.

package go_deepequalerrors

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

_errNew: {
	node: "call_expression"
	fields: function: {
		node: "selector_expression"
		fields: {
			operand: {capture: "epkg", pattern: gopat.Identifier}
			field:   {capture: "efn", pattern: gopat.FieldIdentifier}
		}
	}
	where: [
		{op: "eq", args: ["@epkg", "errors"]},
		{op: "eq", args: ["@efn", "New"]},
	]
}

_errErrorf: {
	node: "call_expression"
	fields: function: {
		node: "selector_expression"
		fields: {
			operand: {capture: "epkg", pattern: gopat.Identifier}
			field:   {capture: "efn", pattern: gopat.FieldIdentifier}
		}
	}
	where: [
		{op: "eq", args: ["@epkg", "fmt"]},
		{op: "eq", args: ["@efn", "Errorf"]},
	]
}

_deep: {
	_arg0: _
	_arg1: _

	out: {
		languages: [golang.Name]
		requires: []
		provides: []

		match: gopat.PackageCall & {
			fields: arguments: {
				node: "argument_list"
				children: [_arg0, _arg1]
			}
			where: [
				{op: "eq", args: ["@pkg", "reflect"]},
				{op: "eq", args: ["@fn", "DeepEqual"]},
			]
		}

		diagnose: {
			message:  "avoid using reflect.DeepEqual with error values"
			severity: "warning"
		}
	}
}

go_deepequalerrors: schema.#Analyzer & {
	name:    "go_deepequalerrors"
	version: "0.1.0"
	doc:     "Flag reflect.DeepEqual on errors.New / fmt.Errorf results"
	facts: {}

	rules: {
		new_first: (_deep & {_arg0: _errNew, _arg1: gopat.Any}).out & {
			name: "new_first"
			doc:  "DeepEqual(errors.New(...), x)"
		}
		new_second: (_deep & {_arg0: gopat.Any, _arg1: _errNew}).out & {
			name: "new_second"
			doc:  "DeepEqual(x, errors.New(...))"
		}
		errorf_first: (_deep & {_arg0: _errErrorf, _arg1: gopat.Any}).out & {
			name: "errorf_first"
			doc:  "DeepEqual(fmt.Errorf(...), x)"
		}
	}
}
