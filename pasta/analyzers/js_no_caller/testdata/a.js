function caller() { return arguments.callee } // want "arguments.callee or arguments.caller"
function caller2() { return arguments.caller } // want "arguments.callee or arguments.caller"
