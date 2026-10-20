// go_envconfig flags typed environment parsing that
// github.com/sethvargo/go-envconfig already does.
//
// The shapes are the ones that show up in small helpers:
//
//	time.ParseDuration(os.Getenv("TIMEOUT"))
//	v := os.Getenv("PORT")
//	n, err := strconv.Atoi(v)
//	if v := os.Getenv("IDLE"); v != "" {
//	    d, err := time.ParseDuration(v)
//	}
//
// A value copied through another variable, or parsed more than one
// statement after the read, is out of reach. Tracking every Getenv
// result by name would also flag unrelated variables with the same
// spelling, because fact names are not scoped. A statement list is
// reported once, at its first pair.

package go_envconfig

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

#getenv: schema.#Pattern & {
	node: "call_expression"
	fields: function: {
		node: "selector_expression"
		fields: {
			operand: {capture: "srcpkg", pattern: gopat.Identifier}
			field:   {capture: "srcfn", pattern: gopat.FieldIdentifier}
		}
	}
	where: [
		{op: "eq", args: ["@srcpkg", "os"]},
		{op: "matches", args: ["@srcfn", "^(Getenv|LookupEnv)$"]},
	]
}

#parseOfIdent: gopat.PackageCall & {
	fields: arguments: {
		node: "argument_list"
		children: [{capture: "arg", pattern: gopat.Identifier}]
	}
	where: [
		{op: "matches", args: ["@pkg", "^(strconv|time)$"]},
		{op: "matches", args: ["@fn", "^(Atoi|ParseBool|ParseInt|ParseUint|ParseFloat|ParseDuration)$"]},
	]
}

#assignGet: schema.#Pattern & {
	node: ["short_var_declaration", "assignment_statement"]
	fields: {
		left: {
			node: "expression_list"
			children: [{capture: "lhs", pattern: gopat.Identifier}]
		}
		right: {
			node: "expression_list"
			children: [#getenv]
		}
	}
}

#assignParse: schema.#Pattern & {
	node: ["short_var_declaration", "assignment_statement"]
	fields: right: {
		node: "expression_list"
		children: [#parseOfIdent]
	}
}

#diagnose: {
	message:  "parsing an environment variable with strconv or time.ParseDuration; use github.com/sethvargo/go-envconfig"
	severity: "warning"
}

go_envconfig: schema.#Analyzer & {
	name:    "go_envconfig"
	version: "0.1.0"
	doc:     "Flag strconv and time.ParseDuration applied to os.Getenv or os.LookupEnv"

	facts: {}

	rules: {
		parse_getenv_call: {
			name: "parse_getenv_call"
			doc:  "time.ParseDuration(os.Getenv(...)) and the strconv equivalents"
			languages: [golang.Name]
			requires: []
			provides: []

			match: gopat.PackageCall & {
				fields: arguments: {
					node: "argument_list"
					children: [#getenv]
				}
				where: [
					{op: "matches", args: ["@pkg", "^(strconv|time)$"]},
					{op: "matches", args: ["@fn", "^(Atoi|ParseBool|ParseInt|ParseUint|ParseFloat|ParseDuration)$"]},
				]
			}

			diagnose: #diagnose
		}

		parse_getenv_next: {
			name: "parse_getenv_next"
			doc:  "strconv or time.ParseDuration on the variable assigned from os.Getenv on the previous line"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: gopat.StmtListContainers
				adjacent: [
					{capture: "getenv", pattern: #assignGet},
					{capture: "parse", pattern: #assignParse},
				]
				where: [{op: "same_ident", args: ["@lhs", "@arg"]}]
			}

			diagnose: #diagnose
		}

		parse_getenv_if: {
			name: "parse_getenv_if"
			doc:  "if v := os.Getenv(...); whose body starts by parsing v"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "if_statement"
				fields: {
					initializer: #assignGet
					consequence: {
						node: "block"
						children: [{
							node: "statement_list"
							children: [#assignParse]
						}]
					}
				}
				where: [{op: "same_ident", args: ["@lhs", "@arg"]}]
			}

			diagnose: #diagnose
		}
	}
}
