// go_time_after_select flags `case <-time.After(...)` inside a select
// statement that is contained within a for loop.
// time.After creates an active timer on each iteration that cannot be
// garbage-collected until it expires; prefer time.NewTimer + timer.Stop
// (or time.NewTicker for fixed intervals).
//
// Two-case select statements are mechanically rewritten to create a
// time.NewTimer before the select, stop it in the other branch, and
// receive from timer.C. Three-or-more-case selects are flagged as
// diagnose-only.

package go_time_after_select

import (
	"list"
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

_afterCase: {
	node: "communication_case"
	fields: communication: {
		node: "receive_statement"
		children: [{
			node: "unary_expression"
			fields: operand: {
				capture: "after_call"
				pattern: {
					node: "call_expression"
					fields: {
						function: {
							node: "selector_expression"
							fields: {
								operand: {capture: "pkg", pattern: {node: "identifier"}}
								field:   {capture: "fn", pattern: {node: "field_identifier"}}
							}
						}
						arguments: {
							capture: "after_args"
							pattern: {
								node: "argument_list"
								children: [{capture: "dur"}]
							}
						}
					}
				}
			}
		}]
	}
}

_otherWithBody: {
	capture: "other_case"
	pattern: {
		node: "communication_case"
		children: [
			{node: ["receive_statement", "send_statement"]},
			{capture: "body"},
		]
	}
}

_otherEmpty: {
	capture: "other_case"
	pattern: {
		node: "communication_case"
	}
}

_afterWhere: [
	{op: "ancestor_is", args: ["@_root", "for_statement"]},
	{op: "named_child_count", args: ["@_root", "2"]},
	{op: "eq", args: ["@pkg", "time"]},
	{op: "eq", args: ["@fn", "After"]},
	{op: "named_child_count", args: ["@after_args", "1"]},
]

_diag: {
	message:  "time.After in a for-select loop will leak memory until timer expires; use time.NewTimer and Stop/Reset instead"
	severity: "warning"
}

go_time_after_select: schema.#Analyzer & {
	name:    "go_time_after_select"
	version: "0.1.0"
	doc:     "Flag and auto-fix time.After in a for-select loop"

	facts: handled: {kind: "handled"}

	rules: {
		// 2-case select: other case (with body) first, time.After second.
		two_case_second_with_body: {
			name:      "two_case_second_with_body"
			doc:       "Rewrite 2-case for-select (other with body, then time.After) to time.NewTimer"
			languages: [golang.Name]
			requires: []
			provides: ["handled"]

			match: {
				node:     "select_statement"
				children: [_otherWithBody, _afterCase]
				where:    _afterWhere
			}

			diagnose: _diag
			emit: [{fact: "handled", attach: "after_call"}]
			rewrite: edits: [
				{position: "before", anchor: "_root", text: "timer := time.NewTimer(@dur)\n"},
				{position: "before", anchor: "body", text: "timer.Stop()\n"},
				{target: "after_call", replacement: "timer.C"},
			]
		}

		// 2-case select: other case (empty body) first, time.After second.
		two_case_second_empty: {
			name:      "two_case_second_empty"
			doc:       "Rewrite 2-case for-select (empty other case, then time.After) to time.NewTimer"
			languages: [golang.Name]
			requires: []
			provides: ["handled"]

			match: {
				node:     "select_statement"
				children: [_otherEmpty, _afterCase]
				where: list.Concat([_afterWhere, [
					{op: "named_child_count", args: ["@other_case", "1"]},
				]])
			}

			diagnose: _diag
			emit: [{fact: "handled", attach: "after_call"}]
			rewrite: edits: [
				{position: "before", anchor: "_root", text: "timer := time.NewTimer(@dur)\n"},
				{position: "after", anchor: "other_case", text: "\ntimer.Stop()"},
				{target: "after_call", replacement: "timer.C"},
			]
		}

		// 2-case select: time.After first, other case (with body) second.
		two_case_first_with_body: {
			name:      "two_case_first_with_body"
			doc:       "Rewrite 2-case for-select (time.After, then other with body) to time.NewTimer"
			languages: [golang.Name]
			requires: []
			provides: ["handled"]

			match: {
				node:     "select_statement"
				children: [_afterCase, _otherWithBody]
				where:    _afterWhere
			}

			diagnose: _diag
			emit: [{fact: "handled", attach: "after_call"}]
			rewrite: edits: [
				{position: "before", anchor: "_root", text: "timer := time.NewTimer(@dur)\n"},
				{position: "before", anchor: "body", text: "timer.Stop()\n"},
				{target: "after_call", replacement: "timer.C"},
			]
		}

		// 2-case select: time.After first, other case (empty body) second.
		two_case_first_empty: {
			name:      "two_case_first_empty"
			doc:       "Rewrite 2-case for-select (time.After, then empty other case) to time.NewTimer"
			languages: [golang.Name]
			requires: []
			provides: ["handled"]

			match: {
				node:     "select_statement"
				children: [_afterCase, _otherEmpty]
				where: list.Concat([_afterWhere, [
					{op: "named_child_count", args: ["@other_case", "1"]},
				]])
			}

			diagnose: _diag
			emit: [{fact: "handled", attach: "after_call"}]
			rewrite: edits: [
				{position: "before", anchor: "_root", text: "timer := time.NewTimer(@dur)\n"},
				{position: "after", anchor: "other_case", text: "\ntimer.Stop()"},
				{target: "after_call", replacement: "timer.C"},
			]
		}

		// Fallback: 3+ cases or other shapes — diagnose-only.
		for_select_other: {
			name:      "for_select_other"
			doc:       "Flag remaining time.After calls in a for-select loop"
			languages: [golang.Name]
			requires: ["handled"]
			provides: []

			match: {
				node: "call_expression"
				fields: {
					function: {
						node: "selector_expression"
						fields: {
							operand: {capture: "pkg", pattern: {node: "identifier"}}
							field:   {capture: "fn", pattern: {node: "field_identifier"}}
						}
					}
				}
				where: [
					{op: "eq", args: ["@pkg", "time"]},
					{op: "eq", args: ["@fn", "After"]},
					{op: "ancestor_is", args: ["@_root", "communication_case"]},
					{op: "ancestor_is", args: ["@_root", "for_statement"]},
					{op: "not_has_fact", args: ["@_root", "handled"]},
				]
			}

			diagnose: _diag
		}
	}
}
