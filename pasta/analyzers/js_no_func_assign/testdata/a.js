function declaredFn() { return 1 }

function okFn() {
    return declaredFn()
}

function case_func_assign() {
    declaredFn = 2 // want "reassigning a function declaration"
}
