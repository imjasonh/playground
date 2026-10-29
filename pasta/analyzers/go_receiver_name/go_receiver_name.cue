// go_receiver_name flags a method receiver named `this`, `self`, or `_`.
//
// Google Go style: a receiver is a short abbreviation of the type, and
// the same name is used on every method. `this` and `self` are the
// examples the guide marks as worse. An underscore is not a name; omit
// the receiver when the method does not use it.
// https://google.github.io/styleguide/go/decisions#receiver-names

package go_receiver_name

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_receiver_name: schema.#Analyzer & {
	name:    "go_receiver_name"
	version: "0.1.0"
	doc:     "Flag method receivers named this, self, or _"
	facts: {}

	rules: {
		this_or_self: {
			name:      "go_receiver_name"
			doc:       "receiver named this or self"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "method_declaration"
				fields: receiver: {
					node: "parameter_list"
					children: [{
						node: "parameter_declaration"
						fields: name: {capture: "recv"}
					}]
				}
				where: [{op: "matches", args: ["@recv", "^(this|self)$"]}]
			}

			diagnose: {
				message:  "receiver should be a short abbreviation of the type, not this or self"
				severity: "warning"
			}
		}

		blank: {
			name:      "go_receiver_name"
			doc:       "blank receiver name"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "method_declaration"
				fields: receiver: {
					node: "parameter_list"
					children: [{
						node: "parameter_declaration"
						fields: name: {capture: "recv"}
					}]
				}
				where: [{op: "token_eq", args: ["@recv", "_"]}]
			}

			diagnose: {
				message:  "omit an unused receiver instead of naming it _"
				severity: "warning"
			}
		}
	}
}
