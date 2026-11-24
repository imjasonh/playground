use foo::{Foo, bar::Bar}; // want "more than one module"

use foo::bar::{Bar, Baz};

use foo::Bar;

use crate::pack::{delta::apply_delta, EntryRecord}; // want "more than one module"
