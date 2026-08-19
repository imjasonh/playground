// Package hcl declares the built-in HCL language config for pasta.
//
// HashiCorp Configuration Language is the syntax behind Terraform,
// OpenTofu, Packer, Nomad, and Vault. Terraform `.tf` and `.tfvars`
// files use the same grammar via lang/terraform.
package hcl

import "github.com/imjasonh/pasta/schema"

Config: schema.#Language & {
	grammar:    "hcl"
	extensions: [".hcl"]
	comment_types: ["comment"]
}

Name: Config.grammar
