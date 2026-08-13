//! Generate an ADMIN_PASSWORD_HASH matching `y_worker::verify_password`.
//!
//! ```bash
//! cargo run --example hash-password -- 'your-admin-password'
//! ```

use std::env;
use std::io::{self, Read};

fn main() {
    let mut args = env::args().skip(1);
    let password = match args.next() {
        Some(p) => p,
        None => {
            let mut buf = String::new();
            io::stdin()
                .read_to_string(&mut buf)
                .expect("read password from stdin");
            buf.trim().to_string()
        }
    };
    if password.is_empty() {
        eprintln!("usage: hash-password <password>   (or pipe via stdin)");
        std::process::exit(2);
    }
    println!("{}", y_worker::hash_password(&password));
}
