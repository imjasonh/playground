function sparse() { return [1,, 2] } // want "sparse array literal"
function leadingHole() { return [, 1] } // want "sparse array literal"
