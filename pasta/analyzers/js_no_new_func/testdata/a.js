function newFn() { return new Function("return 1") } // want "Function constructor"
function fnCtor() { return Function("return 1") } // want "Function() call"
