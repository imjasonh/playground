; Token-level highlights for TypeScript.

(comment) @comment
[(string) (template_string)] @string
(number) @number

(required_parameter pattern: (identifier) @variable.parameter)
(optional_parameter pattern: (identifier) @variable.parameter)

[
  "function"
  "return"
  "if"
  "else"
  "for"
  "while"
  "do"
  "switch"
  "case"
  "default"
  "break"
  "continue"
  "class"
  "extends"
  "implements"
  "interface"
  "type"
  "enum"
  "new"
  "const"
  "let"
  "var"
  "import"
  "export"
  "from"
  "as"
  "async"
  "await"
  "yield"
  "throw"
  "try"
  "catch"
  "finally"
  "typeof"
  "instanceof"
  "in"
  "of"
  "readonly"
  "public"
  "private"
  "protected"
] @keyword
