function use(value) { return value }

function finOk() { try { use(1) } finally { use(2) } }
