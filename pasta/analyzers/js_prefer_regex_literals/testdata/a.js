function reCtor() { return new RegExp("a+") } // want "RegExp constructor with a string literal"
function reCall() { return RegExp("a+") } // want "RegExp() call with a string literal"
