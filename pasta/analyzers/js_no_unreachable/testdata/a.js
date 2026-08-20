function use(value) { return value }

function afterRet() { return 1; use(2) } // want "statement after return/throw/break/continue"
function afterThrow() { throw new Error("x"); use(2) } // want "statement after return/throw/break/continue"
