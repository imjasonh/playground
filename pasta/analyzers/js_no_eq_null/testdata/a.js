function use(value) { return value }

function eqNull(x) { if (x == null) { use(x) } } // want "== null / != null"
