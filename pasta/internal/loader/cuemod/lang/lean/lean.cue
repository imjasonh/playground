// Package lean declares the built-in Lean 4 language config for pasta.
//
// The grammar parses tactic blocks as terms, so a tactic such as
// `rw [if_pos h]` is an `app` of identifiers, not a dedicated node.
package lean

import "github.com/imjasonh/pasta/schema"

Config: schema.#Language & {
	grammar:    "lean"
	extensions: [".lean"]
	comment_types: ["line_comment", "block_comment", "doc_comment", "module_doc_comment"]
	definition_types: ["def", "theorem", "abbrev"]
}

Name: Config.grammar
