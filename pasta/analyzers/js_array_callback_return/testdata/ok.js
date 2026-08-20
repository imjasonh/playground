function use(value) { return value }

function okMap(xs) { return xs.map((n) => n + 1) }
function okMapRet(xs) { return xs.map((n) => { return n + 1 }) }
function forEachOk(xs) { xs.forEach((n) => { use(n) }) }
