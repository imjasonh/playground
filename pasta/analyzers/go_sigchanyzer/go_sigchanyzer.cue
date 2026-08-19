// go_sigchanyzer is a syntactic port of
// golang.org/x/tools/go/analysis/passes/sigchanyzer.
//
// `signal.Notify` requires a buffered channel so a signal that
// arrives before the receiver is ready is not dropped. Pasta flags
// `signal.Notify(make(chan T))` where `make` has no capacity
// argument, and inserts `, 1`.

package go_sigchanyzer

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_sigchanyzer: schema.#Analyzer & {
	name:    "go_sigchanyzer"
	version: "0.1.0"
	doc:     "Flag unbuffered make(chan T) passed to signal.Notify"

	facts: {}

	rules: unbuffered_make: {
		name: "unbuffered_make"
		doc:  "signal.Notify(make(chan T)) drops signals; buffer the channel"
		languages: [golang.Name]
		requires: []
		provides: []

		match: gopat.PackageCall & {
			fields: arguments: {
				node: "argument_list"
				children: [{
					capture: "mk"
					pattern: {
						node: "call_expression"
						fields: {
							function: {capture: "make", pattern: gopat.Identifier}
							arguments: {
								capture: "mkargs"
								pattern: {
									node: "argument_list"
									children: [{capture: "typ"}]
								}
							}
						}
						where: [
							{op: "eq", args: ["@make", "make"]},
							{op: "named_child_count", args: ["@mkargs", "1"]},
						]
					}
				}]
			}
			where: [
				{op: "eq", args: ["@pkg", "signal"]},
				{op: "eq", args: ["@fn", "Notify"]},
			]
		}

		diagnose: {
			message:  "misuse of unbuffered os.Signal channel as argument to signal.Notify"
			severity: "warning"
		}

		rewrite: edits: [{
			position: "after"
			anchor:   "typ"
			text:     ", 1"
		}]
	}
}
