//! Generate a fresh VAPID key pair for the push backend.
//!
//! ```bash
//! cargo run --example genvapid
//! ```
//!
//! Store the private key as the `VAPID_PRIVATE_KEY` Worker secret and hand the
//! public key to the browser front-end as `applicationServerKey`.

use web_push_worker::VapidKey;

fn main() {
    let key = VapidKey::generate();
    println!("# VAPID key pair (P-256). Keep the private key secret.");
    println!("VAPID_PRIVATE_KEY={}", key.private_key_base64url());
    println!("VAPID_PUBLIC_KEY={}", key.public_key_base64url());
    println!();
    println!(
        "# Browser: pushManager.subscribe({{ applicationServerKey: \"{}\" }})",
        key.public_key_base64url()
    );
}
