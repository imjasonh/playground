// Package tsx declares the built-in TSX language config.
// Tree-sitter's TypeScript grammar does not accept JSX; TSX files
// need the dedicated tsx grammar (compiled into ts-core.wasm).
package tsx

import "github.com/imjasonh/pasta/schema"

Config: schema.#Language & {
	grammar:    "tsx"
	extensions: [".tsx"]
	comment_types: ["comment"]
}

Name: Config.grammar
