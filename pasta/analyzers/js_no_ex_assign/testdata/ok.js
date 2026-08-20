function use(value) { return value }

function exOk() { try { use(1) } catch (errOk) { use(errOk) } }
