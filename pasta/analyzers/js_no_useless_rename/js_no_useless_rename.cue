// js_no_useless_rename flags import { x as x }.
// ESLint `no-useless-rename` covers the same ground.

package js_no_useless_rename

import (
	"github.com/imjasonh/pasta/schema"
	jslang "github.com/imjasonh/pasta/lang/javascript"
	tslang "github.com/imjasonh/pasta/lang/typescript"
	tsxlang "github.com/imjasonh/pasta/lang/tsx"
)

_langs: [jslang.Name, tslang.Name, tsxlang.Name]

_base: {
	languages: _langs
}

js_no_useless_rename: schema.#Analyzer & {
	name:    "js_no_useless_rename"
	version: "0.1.0"
	doc:     "import { x as x }"
	facts: {}
	rules: {
	js_no_useless_rename_import: _base & {
		name: "js_no_useless_rename_import"
		doc:  "import { x as x }"
		requires: []
		provides: []
		match: {
			node: "import_specifier"
			fields: {
				name: {capture: "name", pattern: {node: "identifier"}}
				alias: {capture: "alias", pattern: {node: "identifier"}}
			}
			where: [{op: "same_ident", args: ["@name", "@alias"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "import { x as x }"
		}
	}
	js_no_useless_rename_export: _base & {
		name: "js_no_useless_rename_export"
		doc:  "export { x as x }"
		requires: []
		provides: []
		match: {
			node: "export_specifier"
			fields: {
				name: {capture: "name", pattern: {node: "identifier"}}
				alias: {capture: "alias", pattern: {node: "identifier"}}
			}
			where: [{op: "same_ident", args: ["@name", "@alias"]}]
		}
		diagnose: {
			severity: "hint"
			message:  "export { x as x }"
		}
	}
	}
}
