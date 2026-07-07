; Token-level highlights for JavaScript.

(comment) @comment
[(string) (template_string)] @string
(number) @number

(formal_parameters (identifier) @variable.parameter)

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
] @keyword
