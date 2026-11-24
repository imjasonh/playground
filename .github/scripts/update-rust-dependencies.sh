#!/usr/bin/env bash
# Update, lint, build, and test every top-level Rust app, and update the
# Wrangler version that the Cloudflare Worker apps deploy with.
#
# Runs `cargo update` (the lockfile-level analog of `go get -u`) then verifies
# the app the same way the test workflow gates it, so an update is only pushed
# when it still passes. ESP32 firmware crates get the newest stable host
# toolchain and their host checks, but no `cargo update`: their firmware
# builds need the Xtensa toolchain and ESP-IDF, which this job doesn't
# install. Writes a "result" step output.
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

# Bump the pinned Wrangler before the loop, so every Worker app's deploy
# check runs with the new version.
echo "::group::Update Wrangler"
if (
  cd .github/wrangler
  npx --yes npm-check-updates@latest --upgrade
); then
  echo "- ✅ Wrangler: $(jq -r '.devDependencies.wrangler' .github/wrangler/package.json)" >> "$GITHUB_STEP_SUMMARY"
else
  result=failure
  echo "::error title=Dependency update failed::Wrangler: npm-check-updates"
  echo "- ❌ Wrangler: update failed" >> "$GITHUB_STEP_SUMMARY"
fi
echo "::endgroup::"

# Each app's rust-toolchain.toml follows the stable release that deps.yaml
# installs, so the checks below run with the newest compiler and lints.
stable=$(rustc +stable --version | awk '{print $2}')
if [ -z "$stable" ]; then
  result=failure
  echo "::error title=Rust version lookup failed::rustc +stable --version"
  echo "- ❌ Could not read the stable Rust version." >> "$GITHUB_STEP_SUMMARY"
fi

# bump_toolchain raises the channel in $1/rust-toolchain.toml to $stable when
# it is older.
bump_toolchain() {
  local app="$1" toolchain="$1/rust-toolchain.toml" channel
  channel=$(sed -n 's/^channel = "\([0-9.]*\)"$/\1/p' "$toolchain" 2>/dev/null)
  if [ -n "$stable" ] && [ -n "$channel" ] &&
    [ "$(printf '%s\n%s\n' "$channel" "$stable" | sort -V | tail -n 1)" != "$channel" ]; then
    sed -i "s/^channel = \"${channel}\"$/channel = \"${stable}\"/" "$toolchain"
    echo "- ✅ \`${app}\`: Rust ${channel} → ${stable}" >> "$GITHUB_STEP_SUMMARY"
  fi
}

for app in "${apps[@]}"; do
  echo "::group::Update and verify ${app}"

  bump_toolchain "$app"

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
  # clippy/build plus `wrangler deploy --dry-run` with the pinned Wrangler).
  # The helper removes its decoy package.json on exit, so a failure pull
  # request never commits it.
  # Bash ignores `set -e` inside an `if` condition, so run the subshell as its
  # own command and check its status afterward.
  if [ -f "$app/wrangler.toml" ]; then
    (
      set -euo pipefail
      cd "$app"
      rustup target add wasm32-unknown-unknown
      cargo clippy --target wasm32-unknown-unknown -- -D warnings
      cargo build --release --target wasm32-unknown-unknown
      bash "$repo_root/.github/scripts/check-worker-deploy-build.sh"
    )
    worker_status=$?
    if [ "$worker_status" -eq 0 ]; then
      echo "- ✅ \`${app}\`: wasm + wrangler deploy --dry-run passed" >> "$GITHUB_STEP_SUMMARY"
    else
      result=failure
      echo "::error title=Worker build failed::${app}: wasm32 clippy/build or wrangler deploy --dry-run"
      echo "- ❌ \`${app}\`: wasm + wrangler deploy --dry-run failed" >> "$GITHUB_STEP_SUMMARY"
    fi
  fi

  echo "::endgroup::"
done

if esp32_json=$(bash .github/scripts/discover-esp32-apps.sh --all) &&
  esp32_lines=$(printf '%s' "$esp32_json" | jq -r '.[]'); then
  while IFS= read -r app; do
    [ -n "$app" ] || continue
    echo "::group::Verify ${app} on the host"
    bump_toolchain "$app"
    if bash .github/scripts/test-esp32-host.sh "$app"; then
      echo "- ✅ \`${app}\`: host checks passed" >> "$GITHUB_STEP_SUMMARY"
    else
      result=failure
      echo "::error title=ESP32 host checks failed::${app}: test-esp32-host.sh"
      echo "- ❌ \`${app}\`: host checks failed" >> "$GITHUB_STEP_SUMMARY"
    fi
    echo "::endgroup::"
  done <<< "$esp32_lines"
else
  result=failure
  echo "::error title=ESP32 discovery failed::Could not discover ESP32 firmware crates."
  echo "- ❌ Could not discover ESP32 firmware crates." >> "$GITHUB_STEP_SUMMARY"
fi

echo "result=${result}" >> "$GITHUB_OUTPUT"
