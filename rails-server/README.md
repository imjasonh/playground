# rails-server

Rust rules engine, strategic AI simulator, browser Wasm bindings, and Cloudflare Worker multiplayer server (SQLite Durable Objects with WebSocket Hibernation) for [Rails](../rails/).

## Commands
```bash
# Run unit & integration tests
cargo test

# Run the 1,000-game AI simulator with per-turn invariant verification
cargo run --release --features sim --bin rails-sim -- --games 1000

# Build Cloudflare Worker bundle
bash scripts/worker-build.sh
```
