fn greet(name: &str) -> String {
    format!("hello, {}", name)
}

fn main() {
    for i in 0..3 {
        println!("{} {}", i, greet("world"));
    }
}
