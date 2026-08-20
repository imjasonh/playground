function use(value) { return value }

function caseLet(x) { switch (x) { case 1: let y = 1; use(y); break; default: break } } // want "lexical declaration in a case clause"
