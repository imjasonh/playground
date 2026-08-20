function use(value) { return value }

function nanOk(x) { if (Number.isNaN(x)) { use(x) } }
