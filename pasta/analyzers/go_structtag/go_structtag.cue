// go_structtag is a syntactic port of
// golang.org/x/tools/go/analysis/passes/structtag.
//
// Two checks that do not need types:
//
//   - malformed: `key:"value"` pairs must be space-separated. A tag
//     like `json:"a"xml:"b"` parses as a surprising key.
//   - unexported_json: a lowercase field with a non-ignored `json:`
//     or `xml:` name is invisible to encoding/json and encoding/xml.

package go_structtag

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_structtag: schema.#Analyzer & {
	name:    "go_structtag"
	version: "0.1.0"
	doc:     "Flag malformed struct tags and json/xml tags on unexported fields"
	facts: {}

	rules: {
		missing_space: {
			name: "missing_space"
			doc:  "struct tag key:\"value\" pairs must be separated by spaces"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "field_declaration"
				fields: tag: {capture: "tag"}
				where: [{op: "matches", args: ["@tag", "[A-Za-z0-9_]+:\"[^\"]*\"[A-Za-z]"]}]
			}

			diagnose: {
				message:  "struct field tag not compatible with reflect.StructTag.Get: key:\"value\" pairs not separated by spaces"
				severity: "warning"
			}
		}

		unexported_json: {
			name: "unexported_json"
			doc:  "json or xml tags on unexported fields are ignored"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "field_declaration"
				fields: {
					name: {capture: "name"}
					tag:  {capture: "tag"}
				}
				where: [
					{op: "matches", args: ["@name", "^[a-z]"]},
					{op: "matches", args: ["@tag", "(json|xml):\"[^\"-]"]},
				]
			}

			diagnose: {
				message:  "struct field @name has json or xml tag but is not exported"
				severity: "warning"
			}
		}
	}
}
