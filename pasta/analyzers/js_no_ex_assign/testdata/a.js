function use(value) { return value }

function exAssign() { try { use(1) } catch (errBind) { errBind = 1 } } // want "reassigning a catch binding"
