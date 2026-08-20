function newObj() { return new Object() } // want "Object() / new Object() with no arguments"
function objCall() { return Object() } // want "Object() call with no arguments"
