function use(value) { return value }

function hasDefault(x) { switch (x) { case 1: use(x); break; default: break } }
