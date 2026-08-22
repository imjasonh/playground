function use(value) { return value }

function noDefault(x) { switch (x) { case 1: use(x); break } } // want "switch without a default clause"
