// Package toml declares the built-in TOML language config.
package toml

import "github.com/imjasonh/pasta/schema"

Config: schema.#Language & {
	grammar:    "toml"
	extensions: [".toml"]
	comment_types: ["comment"]
}

Name: Config.grammar
