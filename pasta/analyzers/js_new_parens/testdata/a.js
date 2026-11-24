const a = new Foo; // want "omits ()"
const b = new Foo();
const c = new Foo().bar();
const d = new Foo.Bar();
new Foo; // want "omits ()"
