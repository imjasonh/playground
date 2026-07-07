; Scope/definition/reference model for Rust.

[
  (function_item)
  (closure_expression)
  (block)
  (if_expression)
  (match_expression)
  (match_arm)
  (loop_expression)
  (while_expression)
  (for_expression)
] @local.scope

; Definitions
(function_item name: (identifier) @local.definition)
(parameter pattern: (identifier) @local.definition)
(let_declaration pattern: (identifier) @local.definition)
(for_expression pattern: (identifier) @local.definition)
(closure_parameters (identifier) @local.definition)

; References
(identifier) @local.reference
