function use(value) { return value }

function forInBad(o) { for (const k in o) { use(k) } } // want "for-in body is not guarded by an if"
