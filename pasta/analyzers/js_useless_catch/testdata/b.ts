function typed() {
    try {
        foo();
    } catch (e: unknown) { // want "catch clause only rethrows"
        throw e;
    }
}

function typedWraps() {
    try {
        foo();
    } catch (err: unknown) {
        throw new Error(String(err));
    }
}
