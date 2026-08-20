function use(value) { return value }

function forInOk(o) { for (const k in o) { if (Object.hasOwn(o, k)) { use(k) } } }
function forOfOk(items) { for (const item of items) { use(item) } }
