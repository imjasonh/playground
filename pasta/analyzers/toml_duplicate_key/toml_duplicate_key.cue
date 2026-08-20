// toml_duplicate_key flags consecutive keys with the same name in one
// table (`name = "a"` followed immediately by `name = "b"`). TOML
// forbids duplicate keys; parsers disagree on last-wins vs error.
// Taplo reports the same class of bug. Non-consecutive duplicates are
// not seen (pasta matches adjacent pairs only). No auto-fix.

package toml_duplicate_key

import (
	"github.com/imjasonh/pasta/schema"
	tomllang "github.com/imjasonh/pasta/lang/toml"
)

_dupPairs: {
	_node: string
	_name: string
	_doc:  string

	out: {
		name:      _name
		doc:       _doc
		languages: [tomllang.Name]
		requires: []
		provides: []

		match: {
			node: _node
			adjacent: [
				{
					capture: "first"
					pattern: {
						node: "pair"
						children: [{
							capture: "k1"
							pattern: {node: "bare_key"}
						}]
					}
				},
				{
					capture: "second"
					pattern: {
						node: "pair"
						children: [{
							capture: "k2"
							pattern: {node: "bare_key"}
						}]
					}
				},
			]
			where: [{op: "same_ident", args: ["@k1", "@k2"]}]
		}

		diagnose: {
			severity: "error"
			message:  "duplicate key `@k1`"
		}
	}
}

toml_duplicate_key: schema.#Analyzer & {
	name:    "toml_duplicate_key"
	version: "0.1.0"
	doc:     "Flag consecutive duplicate keys in a TOML table"
	facts: {}

	rules: {
		doc_pairs: (_dupPairs & {
			_node: "document"
			_name: "doc_pairs"
			_doc:  "duplicate keys at document scope"
		}).out

		table_pairs: (_dupPairs & {
			_node: "table"
			_name: "table_pairs"
			_doc:  "duplicate keys inside [table]"
		}).out
	}
}
