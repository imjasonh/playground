function use(value) { return value }

function cmpNegZero(x) { if (x === -0) { use(x) } } // want "do not compare against -0"
function cmpNegZeroL(x) { if (-0 === x) { use(x) } } // want "do not compare against -0 on the left"
