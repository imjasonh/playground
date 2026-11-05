#!/usr/bin/env bash
# Tests for prune-cargo-cache.sh.
# Run: bash .github/scripts/prune-cargo-cache_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
prune="$script_dir/prune-cargo-cache.sh"

failures=0
assert_eq() {
  local got="$1" want="$2" label="$3"
  if [[ "$got" != "$want" ]]; then
    echo "FAIL: $label" >&2
    echo "  got:  $got" >&2
    echo "  want: $want" >&2
    failures=$((failures + 1))
  fi
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

mkdir -p "$tmp/repo/demo"
cat >"$tmp/repo/demo/Cargo.toml" <<'EOF'
[package]
name = "demo-app"
version = "0.1.0"
EOF
cat >"$tmp/repo/demo/Cargo.lock" <<'EOF'
version = 4

[[package]]
name = "aes-gcm"
version = "0.10.0"

[[package]]
name = "demo-app"
version = "0.1.0"

[[package]]
name = "serde"
version = "1.0.0"
EOF

mkdir -p \
  "$tmp/target/debug/deps" \
  "$tmp/target/debug/.fingerprint/serde-aaaaaaaaaaaaaaaa" \
  "$tmp/target/debug/.fingerprint/aes-gcm-bbbbbbbbbbbbbbbb" \
  "$tmp/target/debug/.fingerprint/demo-app-cccccccccccccccc" \
  "$tmp/target/debug/build/serde-aaaaaaaaaaaaaaaa" \
  "$tmp/target/debug/examples" \
  "$tmp/target/debug/incremental/demo-app-cccccccccccccccc" \
  "$tmp/target/wasm32-unknown-unknown/release/deps" \
  "$tmp/registry/cache/index.crates.io-hash" \
  "$tmp/registry/src/index.crates.io-hash/serde-1.0.0" \
  "$tmp/registry/src/index.crates.io-hash/old-crate-9.9.9" \
  "$tmp/registry/index/index.crates.io-hash/se"

echo rlib >"$tmp/target/debug/deps/libserde-aaaaaaaaaaaaaaaa.rlib"
echo rlib >"$tmp/target/debug/deps/libaes_gcm-bbbbbbbbbbbbbbbb.rlib"
echo rlib >"$tmp/target/debug/deps/libdemo_app-cccccccccccccccc.rlib"
echo depinfo >"$tmp/target/debug/deps/demo_app.d"
echo bin >"$tmp/target/debug/demo_app"
echo fp >"$tmp/target/debug/.fingerprint/serde-aaaaaaaaaaaaaaaa/lib-serde"
echo fp >"$tmp/target/debug/.fingerprint/aes-gcm-bbbbbbbbbbbbbbbb/lib-aes-gcm"
echo fp >"$tmp/target/debug/.fingerprint/demo-app-cccccccccccccccc/lib-demo-app"
echo out >"$tmp/target/debug/build/serde-aaaaaaaaaaaaaaaa/out"
echo ex >"$tmp/target/debug/examples/demo_app"
echo inc >"$tmp/target/debug/incremental/demo-app-cccccccccccccccc/s"
echo rustc >"$tmp/target/.rustc_info.json"
echo tag >"$tmp/target/CACHEDIR.TAG"
echo wasm >"$tmp/target/wasm32-unknown-unknown/release/deps/libserde-dddddddddddddddd.rlib"
echo wasmapp >"$tmp/target/wasm32-unknown-unknown/release/demo_app.wasm"
echo crate >"$tmp/registry/cache/index.crates.io-hash/serde-1.0.0.crate"
echo old >"$tmp/registry/cache/index.crates.io-hash/old-crate-9.9.9.crate"
echo src >"$tmp/registry/src/index.crates.io-hash/serde-1.0.0/lib.rs"
echo oldsrc >"$tmp/registry/src/index.crates.io-hash/old-crate-9.9.9/lib.rs"
echo idx >"$tmp/registry/index/index.crates.io-hash/se/serde"

CARGO_LOCK_ROOT="$tmp/repo" bash "$prune" "$tmp/target" "$tmp/registry" >/dev/null

list() {
  (cd "$1" && find . -type f | LC_ALL=C sort | tr '\n' ' ')
}

assert_eq "$(list "$tmp/target")" \
  "./.rustc_info.json ./CACHEDIR.TAG ./debug/.fingerprint/aes-gcm-bbbbbbbbbbbbbbbb/lib-aes-gcm ./debug/.fingerprint/serde-aaaaaaaaaaaaaaaa/lib-serde ./debug/build/serde-aaaaaaaaaaaaaaaa/out ./debug/deps/libaes_gcm-bbbbbbbbbbbbbbbb.rlib ./debug/deps/libserde-aaaaaaaaaaaaaaaa.rlib ./wasm32-unknown-unknown/release/deps/libserde-dddddddddddddddd.rlib " \
  "keeps dependency artifacts and drops the app crate, examples, and incremental"
assert_eq "$(list "$tmp/registry")" \
  "./cache/index.crates.io-hash/serde-1.0.0.crate ./index/index.crates.io-hash/se/serde ./src/index.crates.io-hash/serde-1.0.0/lib.rs " \
  "keeps registry sources named by the lockfile and the index"

CARGO_LOCK_ROOT="$tmp/repo" bash "$prune" "$tmp/missing" >/dev/null
assert_eq "$?" "0" "a missing target directory is not an error"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - prune-cargo-cache.sh"
