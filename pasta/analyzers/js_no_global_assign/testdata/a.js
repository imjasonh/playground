function assignUndef() { undefined = 1 } // want "assignment to a read-only global"
function assignNaN() { NaN = 1 } // want "assignment to a read-only global"
