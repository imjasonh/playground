function use(value) { return value }

function dropCause() { try { use(1) } catch (e) { throw new Error("x") } } // want "throwing a new error from catch without passing the cause"
function becauseIsNotCause() { try { use(1) } catch (e) { throw new Error("because") } } // want "throwing a new error from catch without passing the cause"
