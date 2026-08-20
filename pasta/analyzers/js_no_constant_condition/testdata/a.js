function use(value) { return value }

function constIf() { if (true) { use(1) } } // want "constant if-condition"
function constIfFalse() { if (false) { use(1) } } // want "constant if-condition"
function constWhile() { while (0) { break } } // want "constant while-condition"
