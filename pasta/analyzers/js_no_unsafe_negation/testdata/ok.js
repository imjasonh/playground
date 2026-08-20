function use(value) { return value }

function okIn(x, o) { if (!(x in o)) { use(x) } }
