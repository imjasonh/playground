function use(value) { return value }

function defMid(x) { switch (x) { default: break; case 1: use(x); break } } // want "default clause is not last"
