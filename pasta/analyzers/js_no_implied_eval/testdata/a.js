function use(value) { return value }

function timerStr() { setTimeout("use(1)", 0) } // want "setTimeout/setInterval with a string"
