function use(value) { return value }

function useWith(o) { with (o) { use(x) } } // want "with statement"
