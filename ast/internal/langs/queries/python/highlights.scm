; Token-level highlights for Python.

(comment) @comment
(string) @string
[(integer) (float)] @number

(parameters (identifier) @variable.parameter)
(default_parameter name: (identifier) @variable.parameter)
(typed_parameter (identifier) @variable.parameter)

[
  "def"
  "class"
  "return"
  "if"
  "elif"
  "else"
  "for"
  "while"
  "import"
  "from"
  "as"
  "with"
  "try"
  "except"
  "finally"
  "raise"
  "lambda"
  "pass"
  "break"
  "continue"
  "global"
  "nonlocal"
  "yield"
  "assert"
  "del"
  "in"
  "not"
  "and"
  "or"
] @keyword
