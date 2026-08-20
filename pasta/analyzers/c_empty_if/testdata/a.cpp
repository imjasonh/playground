void f(int x) {
    if (x);              // want "empty then-clause"
    if (x) {
        foo();
    }
}

void foo() {}
