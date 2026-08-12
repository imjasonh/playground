function check(x, y) {
    if (x == 5) {                  // want "use strict equality `===`"
        return true;
    }
    if (y != "ok") {               // want "use strict equality `!==`"
        return false;
    }
    if (y != null) {               // OK: nullish idiom, not equivalent to !==
        return false;
    }
    if (x == undefined) {          // OK: nullish idiom
        return false;
    }
    if (x === y) {                 // OK: already strict
        return true;
    }
    if (x !== y) {                 // OK: already strict
        return true;
    }
    return false;
}
