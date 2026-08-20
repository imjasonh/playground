function use(value) { return value }

function selfCmp(x) { if (x === x) { use(x) } } // want "comparison where both sides are the same identifier"
