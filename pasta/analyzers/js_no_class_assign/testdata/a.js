class AssignedCls {}

function okClass() {
    return new AssignedCls()
}

function case_class_assign() {
    AssignedCls = 1 // want "assignment to a class name"
}
