// go_stdmethods is a syntactic port of
// golang.org/x/tools/go/analysis/passes/stdmethods.
//
// Pasta checks a few well-known method names whose signatures are
// visible from the tree without types:
//
//   - `String()` must return `string`
//   - `Error()` must return `string`
//   - `ReadByte()` must return `(byte, error)`
//
// Methods that merely share those names but implement a different
// contract can false-positive; that is also true of the original
// analyzer for names such as Scan.

package go_stdmethods

import (
	"github.com/imjasonh/pasta/schema"
	golang "github.com/imjasonh/pasta/lang/go"
)

go_stdmethods: schema.#Analyzer & {
	name:    "go_stdmethods"
	version: "0.1.0"
	doc:     "Flag String, Error, and ReadByte methods with the wrong signature"
	facts: {}

	rules: {
		string_no_result: {
			name: "string_no_result"
			doc:  "String() should return string"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "method_declaration"
				fields: name: {capture: "name"}
				absent_fields: ["result"]
				where: [{op: "eq", args: ["@name", "String"]}]
			}

			diagnose: {
				message:  "method String() should have signature String() string"
				severity: "warning"
			}
		}

		error_no_result: {
			name: "error_no_result"
			doc:  "Error() should return string"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "method_declaration"
				fields: name: {capture: "name"}
				absent_fields: ["result"]
				where: [{op: "eq", args: ["@name", "Error"]}]
			}

			diagnose: {
				message:  "method Error() should have signature Error() string"
				severity: "warning"
			}
		}

		string_wrong_result: {
			name: "string_wrong_result"
			doc:  "String() returning a non-string type"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "method_declaration"
				fields: {
					name:   {capture: "name"}
					result: {capture: "ret", pattern: {node: "type_identifier"}}
				}
				where: [
					{op: "eq", args: ["@name", "String"]},
					{op: "neq", args: ["@ret", "string"]},
				]
			}

			diagnose: {
				message:  "method String() should have signature String() string"
				severity: "warning"
			}
		}

		readbyte_one_result: {
			name: "readbyte_one_result"
			doc:  "ReadByte() should return (byte, error)"
			languages: [golang.Name]
			requires: []
			provides: []

			match: {
				node: "method_declaration"
				fields: {
					name:   {capture: "name"}
					result: {capture: "ret", pattern: {node: "type_identifier"}}
				}
				where: [{op: "eq", args: ["@name", "ReadByte"]}]
			}

			diagnose: {
				message:  "method ReadByte() should have signature ReadByte() (byte, error)"
				severity: "warning"
			}
		}
	}
}
