// go_hostport is a syntactic port of
// golang.org/x/tools/go/analysis/passes/hostport.
//
// `fmt.Sprintf("%s:%d", host, port)` produces addresses that break
// for IPv6. `net.JoinHostPort` handles both families. Pasta flags
// that sprintf layout (and `%s:%s`) when it is the format string of
// `fmt.Sprintf`.

package go_hostport

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
	gopat "github.com/imjasonh/pasta/patterns/go"
)

go_hostport: schema.#Analyzer & {
	name:    "go_hostport"
	version: "0.1.0"
	doc:     "Flag fmt.Sprintf(\"%s:%d\", host, port); use net.JoinHostPort"

	facts: {}

	rules: sprintf_colon: {
		name: "sprintf_colon"
		doc:  "fmt.Sprintf with %s:%d or %s:%s should be net.JoinHostPort"
		languages: [golang.Name]
		requires: []
		provides: []

		match: gopat.PackageCall & {
			fields: arguments: {
				node: "argument_list"
				children: [{
					capture: "fmt"
					pattern: {node: ["interpreted_string_literal", "raw_string_literal"]}
				}]
			}
			where: [
				{op: "eq", args: ["@pkg", "fmt"]},
				{op: "eq", args: ["@fn", "Sprintf"]},
				{op: "matches", args: ["@fmt", "%s:%[sd]"]},
			]
		}

		diagnose: {
			message:  "address format %s:%d does not work with IPv6; use net.JoinHostPort"
			severity: "warning"
		}
	}
}
