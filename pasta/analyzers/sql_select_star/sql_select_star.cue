// sql_select_star flags `SELECT *` queries (the bare-asterisk
// projection). Star projections are fragile: schema changes in the
// underlying table change query semantics silently, and they pull
// every column even when you only need a few. `SELECT * FROM`
// inside `EXISTS` or `COUNT(*)` is fine — those are aggregates
// against the whole row, not a projection. We match only a
// select_expression whose sole term is a bare all_fields node, which
// excludes function-call wrappers like COUNT(*).

package sql_select_star

import (
	"github.com/imjasonh/pasta/schema"
	sqllang "github.com/imjasonh/pasta/lang/sql"
)

sql_select_star: schema.#Analyzer & {
	name:    "sql_select_star"
	version: "0.1.0"
	doc:     "Flag SELECT * — fragile under schema changes"
	facts: {}

	rules: select_star: {
		name:      "select_star"
		doc:       "SELECT * FROM ..."
		languages: [sqllang.Name]
		requires: []
		provides: []

		// DerekStride tree-sitter-sql (WASM / official C) names the
		// projection list `select_expression` and the star `all_fields`
		// (gotreesitter's older grammar used select_clause_body /
		// asterisk_expression).
		match: {
			node: "select_expression"
			children: [{
				capture: "term"
				pattern: {
					node: "term"
					children: [{
						capture: "star"
						pattern: {node: "all_fields"}
					}]
					where: [{op: "named_child_count", args: ["@_root", "1"]}]
				}
			}]
			where: [{op: "named_child_count", args: ["@_root", "1"]}]
		}

		diagnose: {
			severity: "warning"
			message:  "SELECT * is fragile under schema changes; project the columns you need explicitly"
		}
	}
}
