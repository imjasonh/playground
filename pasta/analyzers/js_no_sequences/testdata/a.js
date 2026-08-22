function use(value) { return value }

function seq() { return (use(1), use(2), 3) } // want "comma (sequence) expression"
