function use(value) { return value }

function finRet() { try { use(1) } finally { return 2 } } // want "control flow in a finally block"
function finThrow() { try { use(1) } finally { throw new Error("x") } } // want "control flow in a finally block"
