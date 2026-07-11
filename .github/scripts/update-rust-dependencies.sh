#!/usr/bin/env bash
# Update, lint, build, and test every top-level Rust app.
#
# Runs `cargo update` (the lockfile-level analog of `go get -u`) then verifies
# the app the same way the test workflow gates it, so an update is only pushed
# when it still passes. Writes "result" and "has_changes" step outputs.
set -uo pipefail

: "${GITHUB_OUTPUT:?GITHUB_OUTPUT must be set}"
: "${GITHUB_STEP_SUMMARY:?GITHUB_STEP_SUMMARY must be set}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

result=success
{
  echo
  echo "### Daily Rust dependency update"
  echo
} >> "$GITHUB_STEP_SUMMARY"

apps=()
if apps_json=$(bash .github/scripts/discover-rust-apps.sh --all); then
  if app_lines=$(printf '%s' "$apps_json" | jq -r '.[]'); then
    if [ -n "$app_lines" ]; then
      mapfile -t apps <<< "$app_lines"
    fi
  else
    result=failure
    echo "::error title=Rust app discovery failed::Discovery returned invalid JSON."
    echo "- ❌ Rust app discovery returned invalid JSON." >> "$GITHUB_STEP_SUMMARY"
  fi
else
  result=failure
  echo "::error title=Rust app discovery failed::Could not discover Rust apps."
  echo "- ❌ Could not discover Rust apps." >> "$GITHUB_STEP_SUMMARY"
fi

if [ "${#apps[@]}" -eq 0 ]; then
  echo "No Rust apps found."
  if [ "$result" = success ]; then
    echo "- No Rust apps found." >> "$GITHUB_STEP_SUMMARY"
  fi
fi

for app in "${apps[@]}"; do
  echo "::group::Update and verify ${app}"

  if (
    cd "$app"
    cargo update
  ); then
    echo "- ✅ \`${app}\`: dependencies updated" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Dependency update failed::${app}: cargo update"
    echo "- ❌ \`${app}\`: dependency update failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  if (
    cd "$app"
    cargo clippy --all-targets -- -D warnings
  ); then
    echo "- ✅ \`${app}\`: clippy passed" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Clippy failed::${app}: cargo clippy --all-targets -- -D warnings"
    echo "- ❌ \`${app}\`: clippy failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  if (
    cd "$app"
    cargo test
  ); then
    echo "- ✅ \`${app}\`: tests passed" >> "$GITHUB_STEP_SUMMARY"
  else
    result=failure
    echo "::error title=Tests failed::${app}: cargo test"
    echo "- ❌ \`${app}\`: tests failed" >> "$GITHUB_STEP_SUMMARY"
  fi

  # Cloudflare Worker apps: same deploy build path as test-rust-apps.sh (wasm
  # clippy/build plus wrangler [build] command with a decoy package.json).
  if [ -f "$app/wrangler.toml" ]; then
    if (
      set -euo pipefail
      cd "$app"
      rustup target add wasm32-unknown-unknown
      cargo clippy --target wasm32-unknown-unknown -- -D warnings
      cargo build --release --target wasm32-unknown-unknown
      printf '%s\n' '{"dependencies":{"wrangler":"4.107.0"}}' > package.json
      build_cmd=$(
        python3 -c "import pathlib, tomllib; print(tomllib.loads(pathlib.Path('wrangler.toml').read_text())['build']['command'])"
      )
      bash -c "$build_cmd"
      rm -f package.json package-lock.json
      test -f build/worker/shim.mjs
    ); then
      echo "- ✅ \`${app}\`: wasm + worker-build passed" >> "$GITHUB_STEP_SUMMARY"
    else
      result=failure
      echo "::error title=Worker build failed::${app}: wasm32 clippy/build or wrangler [build] command"
      echo "- ❌ \`${app}\`: wasm + worker-build failed" >> "$GITHUB_STEP_SUMMARY"
    fi
  fi

  echo "::endgroup::"
done

if [ -n "$(git status --porcelain -- ':(glob)*/Cargo.toml' ':(glob)*/Cargo.lock')" ]; then
  has_changes=true
else
  has_changes=false
fi

echo "result=${result}" >> "$GITHUB_OUTPUT"
echo "has_changes=${has_changes}" >> "$GITHUB_OUTPUT"
