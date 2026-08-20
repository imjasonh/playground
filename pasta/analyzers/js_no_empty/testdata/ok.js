function use(value) { return value }

function filledIf(x) { if (x) { use(x) } }
function commentedIf(x) { if (x) { /* ignore */ } }
