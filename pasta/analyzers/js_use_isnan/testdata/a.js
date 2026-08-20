function use(value) { return value }

function nanRight(x) { if (x === NaN) { use(x) } } // want "compare with isNaN / Number.isNaN instead of NaN"
function nanLeft(x) { if (NaN === x) { use(x) } } // want "compare with isNaN / Number.isNaN instead of NaN on the left"
