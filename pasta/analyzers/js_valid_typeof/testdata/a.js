function use(value) { return value }

function badTypeof(x) { if (typeof x === "strnig") { use(x) } } // want "typeof compared to an invalid string"
