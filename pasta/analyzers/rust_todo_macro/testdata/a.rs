fn good() -> i32 {
    42
}

fn bad_todo() {
    todo!("implement later"); // want "`todo!()` left in code"
}

fn bad_unimpl() {
    unimplemented!(); // want "`unimplemented!()` left in code"
}
