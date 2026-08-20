// js_no_import_assign flags assigning to an imported binding.
// ESLint `no-import-assign` covers the same ground.

package js_no_import_assign

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

js_no_import_assign: schema.#Analyzer & {
	name:    "js_no_import_assign"
	version: "0.1.0"
	doc:     "assigning to an imported binding"
	facts: {
		imported: {kind: "imported"}
	}
	rules: {

	mark_imported: _base & {
		name: "mark_imported"
		doc:  "Record imported binding names"
		requires: []
		provides: ["imported"]
		match: {
			node: "import_clause"
			children: [{capture: "name", pattern: {node: "identifier"}}]
		}
		emit: [{fact: "imported", attach: "name"}]
	}

	mark_imported_spec: _base & {
		name: "mark_imported_spec"
		doc:  "Record named import specifiers"
		requires: []
		provides: ["imported"]
		match: {
			node: "import_specifier"
			fields: {
				name: {capture: "name", pattern: {node: "identifier"}}
			}
			absent_fields: ["alias"]
		}
		emit: [{fact: "imported", attach: "name"}]
	}

	mark_imported_alias: _base & {
		name: "mark_imported_alias"
		doc:  "Record aliased import specifiers"
		requires: []
		provides: ["imported"]
		match: {
			node: "import_specifier"
			fields: {
				alias: {capture: "alias", pattern: {node: "identifier"}}
			}
		}
		emit: [{fact: "imported", attach: "alias"}]
	}
	js_no_import_assign: _base & {
		name: "js_no_import_assign"
		doc:  "assigning to an imported binding"
		requires: ["imported"]
		provides: []
		match: {
			node: "assignment_expression"
			fields: {
				left: {capture: "lhs", pattern: {node: "identifier"}}
			}
			where: [{op: "has_fact", args: ["@lhs", "imported"]}]
		}
		diagnose: {
			severity: "warning"
			message:  "assigning to an imported binding"
		}
	}
	}
}
