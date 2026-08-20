function use(value) { return value }

function outerDecl(x) { if (x) { function nested() { return 1 } use(nested) } } // want "function declaration in a nested block"
