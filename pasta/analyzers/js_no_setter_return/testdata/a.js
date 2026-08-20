const sobj = { set sx(v) { return v } } // want "setter returns a value"
class C { set sx(v) { return v } } // want "setter returns a value"
