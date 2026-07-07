; Token-level highlights for Rust.

[(line_comment) (block_comment)] @comment
[(string_literal) (raw_string_literal) (char_literal)] @string
[(integer_literal) (float_literal)] @number

(parameter pattern: (identifier) @variable.parameter)

[
  "fn"
  "let"
  "const"
  "static"
  "struct"
  "enum"
  "trait"
  "impl"
  "type"
  "mod"
  "use"
  "pub"
  "return"
  "if"
  "else"
  "match"
  "loop"
  "while"
  "for"
  "in"
  "break"
  "continue"
  "where"
  "as"
  "move"
  "unsafe"
  "async"
  "await"
  "dyn"
] @keyword
