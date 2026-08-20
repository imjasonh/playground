function use(value) { return value }

function lone() { { use(1) } } // want "nested standalone block"
