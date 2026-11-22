#!/usr/bin/env bash
# Tests for discover-esp32-apps.sh and the ESP32 exclusion in
# discover-rust-apps.sh.
# Run: bash .github/scripts/discover-esp32-apps_test.sh
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

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

discover() {
  printf '%s\n' "$@" | bash .github/scripts/discover-esp32-apps.sh --from-changes
}

all=$(bash .github/scripts/discover-esp32-apps.sh --all)
assert_eq "$all" '["esp32-ble","mcu-lab"]' "--all lists the crates with an ESP-IDF target"

assert_eq "$(discover esp32-ble/src/protocol.rs)" '["esp32-ble"]' "a change in a crate selects that crate"
assert_eq "$(discover mcu-lab/src/protocol.rs)" '["mcu-lab"]' "a change in mcu-lab selects that crate"
assert_eq "$(discover .github/workflows/mcu-lab-publish.yml)" '["mcu-lab"]' \
  "a change to a crate's publish workflow selects that crate"
assert_eq "$(discover .github/scripts/test-esp32-host.sh)" "$all" "the host test script selects every crate"
assert_eq "$(discover y/src/lib.rs README.md .github/workflows/test.yml)" '[]' \
  "a change outside the crates selects nothing"

rust=$(bash .github/scripts/discover-rust-apps.sh --all)
for app in esp32-ble mcu-lab; do
  assert_eq "$(jq -c --arg a "$app" 'index($a) != null' <<<"$rust")" "false" \
    "discover-rust-apps.sh leaves out $app"
done

if ((failures > 0)); then
  echo "$failures test(s) failed" >&2
  exit 1
fi
echo "ok - discover-esp32-apps.sh"
