function wrapS() { return new String("x") } // want "new String/Number/Boolean"
function wrapN() { return new Number(1) } // want "new String/Number/Boolean"
