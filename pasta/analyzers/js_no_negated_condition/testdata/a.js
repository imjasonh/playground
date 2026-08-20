function use(value) { return value }

function negCond(x) { if (!x) { use(1) } else { use(2) } } // want "if-condition starts with ! and has an else"
