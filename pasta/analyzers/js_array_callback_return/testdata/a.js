function use(value) { return value }

function badMap(xs) { return xs.map((n) => { use(n) }) } // want "array callback with a block body and no return"
