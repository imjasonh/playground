function optCall(x) { return (x?.fn)() } // want "optional chain used as a call callee inside parentheses"
function optMem(x) { return (x?.y).z } // want "optional chain used as a member object inside parentheses"
function optSub(x) { return (x?.[0]).z } // want "optional chain used as a member object inside parentheses"
function optNew(x) { return new (x?.Y)() } // want "optional chain used as a new constructor"
