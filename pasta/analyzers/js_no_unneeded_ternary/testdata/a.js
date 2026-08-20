function boolTern(x) { return x ? true : false } // want "ternary that should be a boolean or ||"
function orTern(x, y) { return x ? x : y } // want "x ? x : y"
