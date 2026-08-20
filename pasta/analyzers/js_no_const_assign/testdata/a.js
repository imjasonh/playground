const frozenVal = 1

function okConst() {
    return frozenVal
}

function case_const_assign() {
    frozenVal = 2 // want "assignment to a const binding"
}
