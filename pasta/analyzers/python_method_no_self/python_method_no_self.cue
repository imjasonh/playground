// python_method_no_self flags methods declared inside a class whose
// first parameter isn't `self` or `cls`.
//
// The first parameter is the first non-comment named child of the
// `parameters` node. Newlines, spaces, and comments around the name
// do not matter. A wrapped `self` is still `self`.
//
// Caveats:
//   - Nested functions inside class methods also have a
//     `class_definition` ancestor, so they fire too. They are
//     closures, not methods.
//   - `@staticmethod` methods are valid without self/cls and fire
//     here. Looking at decorators is a later refinement.

package python_method_no_self

import (
	"github.com/imjasonh/pasta/schema"
	pylang "github.com/imjasonh/pasta/lang/python"
	pypat "github.com/imjasonh/pasta/patterns/python"
)

_inClass: {
	op:   "ancestor_is"
	args: ["@_root", pypat.ClassLikeTypes]
}

_diag: {
	message:  "method `@name` is missing `self` (or `cls`) as first parameter"
	severity: "warning"
}

_base: {
	languages: [pylang.Name]
	requires: []
	provides: []
	diagnose: _diag
}

python_method_no_self: schema.#Analyzer & {
	name:    "python_method_no_self"
	version: "0.2.0"
	doc:     "Flag class methods whose first parameter isn't self/cls"
	facts: {}

	rules: {
		missing_self_empty: _base & {
			name: "missing_self_empty"
			doc:  "Class method with an empty parameter list"
			match: {
				node: "function_definition"
				fields: {
					name: {capture: "name"}
					parameters: {capture: "params"}
				}
				where: [
					_inClass,
					{op: "empty", args: ["@params"]},
				]
			}
		}

		missing_self: _base & {
			name: "missing_self"
			doc:  "Class method whose first parameter is a bare name other than self/cls"
			match: {
				node: "function_definition"
				fields: {
					name: {capture: "name"}
					parameters: {
						node: "parameters"
						children: [{
							capture: "ident"
							pattern: pypat.Identifier
						}]
					}
				}
				where: [
					_inClass,
					{op: "neq", args: ["@ident", "self"]},
					{op: "neq", args: ["@ident", "cls"]},
				]
			}
		}

		missing_self_annotated: _base & {
			name: "missing_self_annotated"
			doc:  "Class method whose first typed or default parameter isn't self/cls"
			match: {
				node: "function_definition"
				fields: {
					name: {capture: "name"}
					parameters: {
						node: "parameters"
						children: [{
							node: [
								"typed_parameter",
								"default_parameter",
								"typed_default_parameter",
							]
							children: [{
								capture: "ident"
								pattern: pypat.Identifier
							}]
						}]
					}
				}
				where: [
					_inClass,
					{op: "neq", args: ["@ident", "self"]},
					{op: "neq", args: ["@ident", "cls"]},
				]
			}
		}

		missing_self_splat: _base & {
			name: "missing_self_splat"
			doc:  "Class method whose first parameter is a splat or a bare / or *"
			match: {
				node: "function_definition"
				fields: {
					name: {capture: "name"}
					parameters: {
						node: "parameters"
						children: [{
							capture: "first"
							pattern: {
								node: [
									"list_splat_pattern",
									"dictionary_splat_pattern",
									"positional_separator",
									"keyword_separator",
									"tuple_pattern",
								]
							}
						}]
					}
				}
				where: [_inClass]
			}
		}

		missing_self_typed_splat: _base & {
			name: "missing_self_typed_splat"
			doc:  "Class method whose first parameter is a typed *args or **kwargs"
			match: {
				node: "function_definition"
				fields: {
					name: {capture: "name"}
					parameters: {
						node: "parameters"
						children: [{
							node: "typed_parameter"
							children: [{
								node: [
									"list_splat_pattern",
									"dictionary_splat_pattern",
								]
							}]
						}]
					}
				}
				where: [_inClass]
			}
		}
	}
}
