fn f(x: bool) {
    // Good
    if x {}
    if !x {}

    // Bad
    if x == true {} // want "redundant comparison to boolean literal"
    if x == false {} // want "redundant comparison to boolean literal"
    if true == x {} // want "redundant comparison to boolean literal"
}
