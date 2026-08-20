function use(value) { return value }

function keepCause() { try { use(1) } catch (e) { throw new Error("x", { cause: e }) } }
