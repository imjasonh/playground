function use(value) { return value }

function condAssign(x, y) { if (x = y) { use(x) } } // want "assignment used as if-condition"
function condAssignWhile(x) { while (x = next()) { use(x) } } // want "assignment used as while-condition"
