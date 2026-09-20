//! Print a random 32-byte hex secret for `wrangler secret put JWT_SECRET`.

use rand_core::{OsRng, RngCore};

fn main() {
    let mut bytes = [0u8; 32];
    OsRng.fill_bytes(&mut bytes);
    for b in bytes {
        print!("{b:02x}");
    }
    println!();
}
