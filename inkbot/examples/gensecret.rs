//! Generate a random shared upload secret for inkbot.
//!
//! ```bash
//! cargo run --example gensecret
//! wrangler secret put UPLOAD_SECRET   # paste the value
//! ```
//!
//! On deploy, `.github/scripts/ensure-worker-upload-secret.sh` runs this when
//! the Worker has no `UPLOAD_SECRET` yet, so the first deploy is hands-free.

use rand_core::{OsRng, RngCore};

fn main() {
    let mut bytes = [0u8; 32];
    OsRng.fill_bytes(&mut bytes);
    println!("UPLOAD_SECRET={}", hex::encode(bytes));
}
