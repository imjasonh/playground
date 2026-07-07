; Scope/definition/reference model for TypeScript.

[
  (program)
  (function_declaration)
  (function_expression)
  (arrow_function)
  (method_definition)
  (statement_block)
  (class_declaration)
  (for_statement)
  (for_in_statement)
  (catch_clause)
] @local.scope

; Definitions
(variable_declarator name: (identifier) @local.definition)
(function_declaration name: (identifier) @local.definition)
(required_parameter pattern: (identifier) @local.definition)
(optional_parameter pattern: (identifier) @local.definition)
(arrow_function parameter: (identifier) @local.definition)
(catch_clause parameter: (identifier) @local.definition)

; References
(identifier) @local.reference
