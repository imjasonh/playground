function f() {
    var x = 5;                  // want "use `let` instead of `var`"
    var y, z = 1;               // want "use `let` instead of `var`"
    let already = 7;
    const constant = 9;
    return x + y + z + already + constant;
}

// Redeclaration that would break under a naive var→let rewrite — still
// diagnosed, but pasta must not autofix this shape.
function g(ctx) {
    var { spanToStart } = ctx.span(); // want "use `let` instead of `var`"
    var { spanToStart } = ctx.span(); // want "use `let` instead of `var`"
    return spanToStart;
}
