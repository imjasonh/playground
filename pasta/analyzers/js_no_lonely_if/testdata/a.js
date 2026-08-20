function use(value) { return value }

function lonely(a, b) { if (a) { use(a) } else { if (b) { use(b) } } } // want "if as the only statement in an else block"
