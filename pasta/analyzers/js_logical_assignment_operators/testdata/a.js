function logAssign(x, y) { x = x && y; return x } // want "x = x && y can be x &&= y"
