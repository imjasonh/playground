function use(value) { return value }

function skip(xs) { for (const x of xs) { if (x) { continue } use(x) } } // want "continue statement"
