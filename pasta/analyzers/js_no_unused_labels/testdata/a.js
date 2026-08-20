function use(value) { return value }

function unusedLab() { unusedLbl: use(1) } // want "labeled statement whose body has no matching break/continue"
