function f() {
    try {
        foo();
    } catch (e) { // want "catch clause only rethrows"
        throw e;
    }
}

function logsThenRethrows() {
    try {
        foo();
    } catch (e) {
        console.log(e);
        throw e;
    }
}

function wraps() {
    try {
        foo();
    } catch (e) {
        throw new Error(e);
    }
}

function optionalCatch() {
    try {
        foo();
    } catch {
        throw e;
    }
}
