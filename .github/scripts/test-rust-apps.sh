#!/usr/bin/env bash
# Format-check, lint, build, and test the Rust apps listed in RUST_APPS as JSON.
#
# Each app's toolchain comes from its rust-toolchain.toml (rustup honors it).
# Cloudflare Worker apps (those with a wrangler.toml) additionally get clippy
# and a release build for the wasm32-unknown-unknown target.
set -uo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

mapfile -t apps < <(printf '%s' "${RUST_APPS:-[]}" | jq -r '.[]')

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No Rust apps changed. Nothing to test."
  exit 0
fi

result=0
for app in "${apps[@]}"; do
  echo "::group::Lint, build, and test ${app}"

  if (
    cd "$app"
    cargo fmt --check
  ); then
    echo "${app}: formatting ok"
  else
    echo "::error title=Rust formatting failed::${app}: cargo fmt --check"
    result=1
  fi

  if (
    cd "$app"
    cargo clippy --locked --all-targets -- -D warnings
  ); then
    echo "${app}: clippy passed"
  else
    echo "::error title=Rust clippy failed::${app}: cargo clippy --locked --all-targets -- -D warnings"
    result=1
  fi

  if (
    cd "$app"
    cargo test --locked
  ); then
    echo "${app}: tests passed"
  else
    echo "::error title=Rust tests failed::${app}: cargo test --locked"
    result=1
  fi

  # Cloudflare Worker apps compile to wasm; verify the deployable artifact too.
  if [ -f "$app/wrangler.toml" ]; then
    if (
      set -euo pipefail
      cd "$app"
      rustup target add wasm32-unknown-unknown
      cargo clippy --locked --target wasm32-unknown-unknown -- -D warnings
      cargo build --locked --release --target wasm32-unknown-unknown
    ); then
      echo "${app}: wasm build passed"
    else
      echo "::error title=Rust wasm build failed::${app}: wasm32-unknown-unknown clippy/build"
      result=1
    fi
  fi

  echo "::endgroup::"
done

exit "$result"
