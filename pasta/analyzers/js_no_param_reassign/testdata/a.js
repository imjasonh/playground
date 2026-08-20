function okParam(paramX) {
    return paramX
}

function case_param_reassign(paramX) {
    paramX = 1 // want "assignment to a function parameter"
}
