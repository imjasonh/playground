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

mkdir -p "$tmp/repo/demo/rust"
cat >"$tmp/repo/demo/rust/Cargo.toml" <<'EOF'
[package]
name = "demo-lib"
version = "0.1.0"
EOF
cat >"$tmp/repo/demo/rust/Cargo.lock" <<'EOF'
version = 4

[[package]]
name = "demo-lib"
version = "0.1.0"

[[package]]
name = "ureq"
version = "2.0.0"
EOF

mkdir -p \
  "$tmp/target/debug/deps" \
  "$tmp/target/debug/.fingerprint/ureq-eeeeeeeeeeeeeeee" \
  "$tmp/target/debug/.fingerprint/demo-lib-ffffffffffffffff" \
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
echo rlib >"$tmp/target/debug/deps/libureq-eeeeeeeeeeeeeeee.rlib"
echo rlib >"$tmp/target/debug/deps/libdemo_lib-ffffffffffffffff.rlib"
echo fp >"$tmp/target/debug/.fingerprint/ureq-eeeeeeeeeeeeeeee/lib-ureq"
echo fp >"$tmp/target/debug/.fingerprint/demo-lib-ffffffffffffffff/lib-demo-lib"
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
  "./.rustc_info.json ./CACHEDIR.TAG ./debug/.fingerprint/aes-gcm-bbbbbbbbbbbbbbbb/lib-aes-gcm ./debug/.fingerprint/serde-aaaaaaaaaaaaaaaa/lib-serde ./debug/.fingerprint/ureq-eeeeeeeeeeeeeeee/lib-ureq ./debug/build/serde-aaaaaaaaaaaaaaaa/out ./debug/deps/libaes_gcm-bbbbbbbbbbbbbbbb.rlib ./debug/deps/libserde-aaaaaaaaaaaaaaaa.rlib ./debug/deps/libureq-eeeeeeeeeeeeeeee.rlib ./wasm32-unknown-unknown/release/deps/libserde-dddddddddddddddd.rlib " \
  "keeps dependency artifacts, including a nested library crate's, and drops the app crates, examples, and incremental"
assert_eq "$(list "$tmp/registry")" \
  "./cache/index.crates.io-hash/serde-1.0.0.crate ./index/index.crates.io-hash/se/serde ./src/index.crates.io-hash/serde-1.0.0/lib.rs " \
  "keeps registry sources named by the lockfile and the index"

CARGO_LOCK_ROOT="$tmp/repo" bash "$prune" "$tmp/missing" >/dev/null
assert_eq "$?" "0" "a missing target directory is not an error"

# Cargo 1.100's layout: one directory per package under build/, one per unit
# under that, and no deps/ or .fingerprint/.
v2="$tmp/target-v2/debug/build"
mkdir -p "$v2/aes-gcm/bbbbbbbbbbbbbbbb/out" "$v2/aes-gcm/bbbbbbbbbbbbbbbb/fingerprint" \
  "$v2/demo-app/cccccccccccccccc/out" "$v2/old-crate/9999999999999999/out" \
  "$v2/serde/aaaaaaaaaaaaaaaa/run"
echo rlib >"$v2/aes-gcm/bbbbbbbbbbbbbbbb/out/libaes_gcm-bbbbbbbbbbbbbbbb.rlib"
echo fp >"$v2/aes-gcm/bbbbbbbbbbbbbbbb/fingerprint/lib-aes-gcm"
echo bin >"$v2/demo-app/cccccccccccccccc/out/demo_app-cccccccccccccccc"
echo rlib >"$v2/old-crate/9999999999999999/out/libold_crate-9999999999999999.rlib"
echo out >"$v2/serde/aaaaaaaaaaaaaaaa/run/stdout"
CARGO_LOCK_ROOT="$tmp/repo" bash "$prune" "$tmp/target-v2" >/dev/null
assert_eq "$(list "$tmp/target-v2")" \
  "./debug/build/aes-gcm/bbbbbbbbbbbbbbbb/fingerprint/lib-aes-gcm ./debug/build/aes-gcm/bbbbbbbbbbbbbbbb/out/libaes_gcm-bbbbbbbbbbbbbbbb.rlib ./debug/build/serde/aaaaaaaaaaaaaaaa/run/stdout " \
  "the build/PACKAGE/HASH layout keeps packages with hyphens and drops the app crates and old packages"

# An ESP32 firmware crate: its lockfile is skipped by default and named with
# -l by its own jobs, together with the standard library's for build-std.
mkdir -p "$tmp/repo/fw/.cargo" "$tmp/sysroot"
cat >"$tmp/repo/fw/.cargo/config.toml" <<'EOF'
[target.xtensa-esp32-espidf]
linker = "ldproxy"
EOF
cat >"$tmp/repo/fw/Cargo.toml" <<'EOF'
[package]
name = "fw"
version = "0.1.0"
EOF
cat >"$tmp/repo/fw/Cargo.lock" <<'EOF'
version = 4

[[package]]
name = "esp-idf-sys"
version = "0.36.0"

[[package]]
name = "fw"
version = "0.1.0"
EOF
cat >"$tmp/sysroot/Cargo.lock" <<'EOF'
version = 4

[[package]]
name = "std"
version = "0.0.0"

[[package]]
name = "rustc-std-workspace-core"
version = "1.99.0"
EOF

mkdir -p "$tmp/default/debug/deps"
echo rlib >"$tmp/default/debug/deps/libserde-aaaaaaaaaaaaaaaa.rlib"
echo rlib >"$tmp/default/debug/deps/libesp_idf_sys-1111111111111111.rlib"
CARGO_LOCK_ROOT="$tmp/repo" bash "$prune" "$tmp/default" >/dev/null
assert_eq "$(list "$tmp/default")" "./debug/deps/libserde-aaaaaaaaaaaaaaaa.rlib " \
  "the default lockfiles leave out an ESP32 firmware crate's"

fw="$tmp/fw-target/fw/xtensa-esp32-espidf/release"
cmake="$fw/build/esp-idf-sys-1111111111111111/out/build"
mkdir -p "$fw/deps" "$fw/.fingerprint/std-2222222222222222" "$cmake/bootloader-prefix/tmp" "$cmake/examples"
echo rlib >"$fw/deps/libstd-2222222222222222.rlib"
echo rlib >"$fw/deps/librustc_std_workspace_core-3333333333333333.rlib"
echo rlib >"$fw/deps/libesp_idf_sys-1111111111111111.rlib"
echo rlib >"$fw/deps/libserde-aaaaaaaaaaaaaaaa.rlib"
echo rlib >"$fw/deps/libfw-4444444444444444.rlib"
echo fp >"$fw/.fingerprint/std-2222222222222222/lib-std"
echo cfg >"$cmake/bootloader-prefix/tmp/bootloader-cfgcmd.txt"
echo ex >"$cmake/examples/readme"
echo bin >"$fw/fw"
bash "$prune" -l "$tmp/repo/fw/Cargo.lock" -l "$tmp/sysroot/Cargo.lock" "$tmp/fw-target" >/dev/null
assert_eq "$(list "$tmp/fw-target")" \
  "./fw/xtensa-esp32-espidf/release/.fingerprint/std-2222222222222222/lib-std ./fw/xtensa-esp32-espidf/release/build/esp-idf-sys-1111111111111111/out/build/bootloader-prefix/tmp/bootloader-cfgcmd.txt ./fw/xtensa-esp32-espidf/release/build/esp-idf-sys-1111111111111111/out/build/examples/readme ./fw/xtensa-esp32-espidf/release/deps/libesp_idf_sys-1111111111111111.rlib ./fw/xtensa-esp32-espidf/release/deps/librustc_std_workspace_core-3333333333333333.rlib ./fw/xtensa-esp32-espidf/release/deps/libstd-2222222222222222.rlib " \
  "-l keeps what the named lockfiles list, and build script output keeps its tmp and examples"

status=0
bash "$prune" -l "$tmp/none/Cargo.lock" "$tmp/fw-target" >/dev/null 2>&1 || status=$?
assert_eq "$status" "1" "a missing -l lockfile is an error"

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - prune-cargo-cache.sh"
