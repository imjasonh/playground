fn bad() {
    let _ = std::panic::catch_unwind(|| 1); // want "catch_unwind"
    let _ = panic::catch_unwind(|| 1); // want "catch_unwind"
}

fn ok() {
    let _ = std::panic::catch_unwind; // the function, not a call
    let _ = something.catch_unwind();
}

fn catch_unwind() {}

fn local() {
    catch_unwind(); // want "catch_unwind"
}
