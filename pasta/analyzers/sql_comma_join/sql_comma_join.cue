// sql_comma_join flags `FROM a, b` — the implicit comma join.
// Comma joins hide the relationship between tables and are easy to
// turn into accidental cross joins. Prefer `FROM a JOIN b ON …`.
// The SQL example in aspect-build/rules_lint uses an explicit JOIN;
// this rule catches the older form. `SELECT *` is `sql_select_star`.

package sql_comma_join

import (
	"github.com/imjasonh/pasta/schema"
	sqllang "github.com/imjasonh/pasta/lang/sql"
)

sql_comma_join: schema.#Analyzer & {
	name:    "sql_comma_join"
	version: "0.1.0"
	doc:     "Flag FROM a, b comma joins — prefer explicit JOIN"
	facts: {}

	rules: comma_from: {
		name:      "comma_from"
		doc:       "FROM a, b is an implicit join"
		languages: [sqllang.Name]
		requires: []
		provides: []

		match: {
			node: "from"
			children: [
				{node: "keyword_from"},
				{node: "relation"},
				{node: "relation"},
			]
		}

		diagnose: {
			severity: "warning"
			message:  "comma join in FROM; write an explicit JOIN with an ON clause"
		}
	}
}
