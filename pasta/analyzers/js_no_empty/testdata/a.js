function emptyIf(x) { if (x) {} } // want "empty if block"
function emptyWhile(x) { while (x) {} } // want "empty while block"
function emptyFor() { for (let i = 0; i < 1; i += 1) {} } // want "empty for block"
