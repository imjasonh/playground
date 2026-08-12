fn main() {
    let x = Some(1).unwrap();        // want ".unwrap()/.expect() panics"
    let y = Ok::<i32, ()>(2).expect("nope"); // want ".unwrap()/.expect() panics"
    let z = Some(3).unwrap_or(0);    // OK
}
