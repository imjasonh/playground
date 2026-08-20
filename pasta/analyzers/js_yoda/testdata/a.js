function use(value) { return value }

function yodaEq(x) { if (1 === x) { use(x) } } // want "literal on the left of a comparison"
