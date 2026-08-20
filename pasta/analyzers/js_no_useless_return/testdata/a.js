function use(value) { return value }

function uselessRet() { use(1); return } // want "empty return as the last statement after another statement"
