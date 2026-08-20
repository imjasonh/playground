function use(value) { return value }

function negIn(x, o) { if (!x in o) { use(x) } } // want "negating the left operand of in / instanceof"
function negInst(x) { if (!x instanceof Number) { use(x) } } // want "negating the left operand of in / instanceof"
