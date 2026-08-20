function use(value) { return value }

function condAssignOk(x, y) { if ((x = y)) { use(x) } }
function condEq(x, y) { if (x === y) { use(x) } }
