function eval() { return 1 } // want "binding named undefined/NaN/Infinity/arguments/eval"
function shadowUndef() { const undefined = 1; return undefined } // want "let/const/var named undefined/NaN/Infinity/arguments/eval"
