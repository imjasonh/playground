fn caller(client: &Client) -> i32 {
    let a = legacy::old_fn(); // want `old_fn is deprecated`
    let b = legacy::new_fn(); // OK
    let c = client.post();    // want `post is deprecated`
    let d = client.send();    // OK
    a + b + c + d
}
