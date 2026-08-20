function ctrlHex() { return /\x00/ } // want "control character in a regular expression"
function ctrlUnicode() { return /\u0001/ } // want "control character in a regular expression"
