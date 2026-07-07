; Scope/definition/reference model for Go, used for scope-aware rename.

; Scopes
[
  (function_declaration)
  (method_declaration)
  (func_literal)
  (block)
  (if_statement)
  (for_statement)
  (expression_switch_statement)
  (type_switch_statement)
  (select_statement)
] @local.scope

; Definitions
(parameter_declaration (identifier) @local.definition)
(variadic_parameter_declaration (identifier) @local.definition)
(short_var_declaration
  left: (expression_list (identifier) @local.definition))
(var_spec name: (identifier) @local.definition)
(const_spec name: (identifier) @local.definition)
(range_clause left: (expression_list (identifier) @local.definition))

; References
(identifier) @local.reference
