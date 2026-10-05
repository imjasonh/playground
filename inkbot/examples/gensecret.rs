//! Generate a random shared upload secret for inkbot.
//!
//! ```bash
//! cargo run --example gensecret
//! wrangler secret put UPLOAD_SECRET   # paste the value
//! ```

fn main() {
    let mut bytes = [0u8; 32];
    getrandom::fill(&mut bytes).expect("read the OS random number generator");
    println!("UPLOAD_SECRET={}", hex::encode(bytes));
}
