; Scope/definition/reference model for Python. Python scopes are function- and
; module-level (not block-level), so blocks are intentionally not scopes.

[
  (module)
  (function_definition)
  (lambda)
  (class_definition)
] @local.scope

; Definitions
(parameters (identifier) @local.definition)
(default_parameter name: (identifier) @local.definition)
(typed_parameter (identifier) @local.definition)
(lambda_parameters (identifier) @local.definition)
(assignment left: (identifier) @local.definition)
(assignment left: (pattern_list (identifier) @local.definition))
(for_statement left: (identifier) @local.definition)
(for_statement left: (pattern_list (identifier) @local.definition))

; References
(identifier) @local.reference
