; Definitions and references for Go, following the tree-sitter "tags"
; convention: the whole definition node is tagged @definition.<kind> and the
; defined name is captured as @name.

(function_declaration
  name: (identifier) @name) @definition.function

(method_declaration
  name: (field_identifier) @name) @definition.method

(type_declaration
  (type_spec
    name: (type_identifier) @name
    type: (struct_type))) @definition.struct

(type_declaration
  (type_spec
    name: (type_identifier) @name
    type: (interface_type))) @definition.interface

(type_declaration
  (type_spec
    name: (type_identifier) @name)) @definition.type

(const_spec
  name: (identifier) @name) @definition.constant

(var_spec
  name: (identifier) @name) @definition.variable

(call_expression
  function: (identifier) @name) @reference.call

(call_expression
  function: (selector_expression
    field: (field_identifier) @name)) @reference.call
