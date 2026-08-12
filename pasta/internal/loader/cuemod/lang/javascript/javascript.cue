// Package javascript declares the built-in JavaScript language config.
package javascript

import "github.com/imjasonh/pasta/schema"

Config: schema.#Language & {
	grammar:    "javascript"
	// .jsx shares the JSX-capable JavaScript grammar.
	extensions: [".js", ".mjs", ".cjs", ".jsx"]
	comment_types: ["comment"]
}

Name: Config.grammar
