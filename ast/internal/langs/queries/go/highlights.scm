; Token-level highlights for Go (subset used for `--kind` token selectors).

(comment) @comment

[
  (interpreted_string_literal)
  (raw_string_literal)
  (rune_literal)
] @string

[
  (int_literal)
  (float_literal)
  (imaginary_literal)
] @number

(parameter_declaration (identifier) @variable.parameter)
(variadic_parameter_declaration (identifier) @variable.parameter)

[
  "func"
  "return"
  "if"
  "else"
  "for"
  "range"
  "type"
  "struct"
  "interface"
  "package"
  "import"
  "const"
  "var"
  "map"
  "chan"
  "go"
  "defer"
  "select"
  "switch"
  "case"
  "default"
  "break"
  "continue"
  "fallthrough"
  "goto"
] @keyword
