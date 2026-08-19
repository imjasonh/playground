// Package terraform declares the Terraform and OpenTofu language config.
//
// Terraform is HCL, so this alias reuses the `hcl` grammar with the
// `.tf` and `.tfvars` extensions. In rule `languages` lists, use
// `Name` (`"terraform"`), not `Config.grammar` (`"hcl"`).
package terraform

import "github.com/imjasonh/pasta/schema"

Config: schema.#Language & {
	grammar: "hcl"
	extensions: [".tf", ".tfvars"]
	comment_types: ["comment"]
}

// Name is the language id used in rule `languages` lists. It is not
// Config.grammar because Terraform is an alias of the hcl grammar.
Name: "terraform"
