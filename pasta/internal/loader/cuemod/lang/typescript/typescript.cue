// Package typescript declares the built-in TypeScript language config.
package typescript

import "github.com/imjasonh/pasta/schema"

Config: schema.#Language & {
	grammar:    "typescript"
	extensions: [".ts"]
	comment_types: ["comment"]
	definition_types: ["function_declaration", "generator_function_declaration", "method_definition"]
}

Name: Config.grammar
