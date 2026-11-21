#!/usr/bin/env bash
# Discover top-level ESP32 firmware crates and emit a JSON array.
#
# An ESP32 firmware crate is a non-hidden top-level directory with Cargo.toml
# whose .cargo/config.toml configures an Xtensa or RISC-V ESP-IDF target. Device
# builds need the espup / ESP-IDF toolchain, so discover-rust-apps.sh leaves
# these out and test.yml's ESP32 jobs test them instead.
#
# Usage:
#   discover-esp32-apps.sh --all
#     List every ESP32 firmware crate in the repo.
#
#   discover-esp32-apps.sh --is-esp32 DIR
#     Exit 0 when DIR is an ESP32 firmware crate.
#
#   discover-esp32-apps.sh --from-changes [path...]
#     List the crates touched by the given paths (or stdin when no args). A
#     change to test-esp32-host.sh selects every crate, and a change to
#     .github/workflows/<crate>-publish.yml selects that crate.
#
# Paths are relative to the working directory, the repository root in CI.
set -euo pipefail

is_esp32_app() {
  local name="$1"
  [[ "$name" != .* && "$name" != */* ]] &&
    [[ -f "$name/Cargo.toml" ]] &&
    grep -Eq '^\[target\.(xtensa|riscv32[a-z]*)-[^]]*-espidf\]' "$name/.cargo/config.toml" 2>/dev/null
}

every_esp32_app() {
  local dir name
  for dir in */; do
    name="${dir%/}"
    if is_esp32_app "$name"; then
      echo "$name"
    fi
  done
}

emit_json() {
  jq -R 'select(. != "")' | jq -cs 'unique'
}

from_changes() {
  local path name
  while IFS= read -r path; do
    case "$path" in
      .github/scripts/test-esp32-host.sh)
        every_esp32_app
        continue
        ;;
      .github/workflows/*-publish.yml)
        name=${path#.github/workflows/}
        name=${name%-publish.yml}
        ;;
      */*) name=${path%%/*} ;;
      *) continue ;;
    esac
    if is_esp32_app "$name"; then
      echo "$name"
    fi
  done
}

mode="${1:---from-changes}"

case "$mode" in
  --all)
    every_esp32_app | emit_json
    ;;
  --is-esp32)
    is_esp32_app "${2:?usage: $0 --is-esp32 DIR}"
    ;;
  --from-changes)
    shift
    if (("$#" > 0)); then
      printf '%s\n' "$@" | from_changes | emit_json
    else
      from_changes | emit_json
    fi
    ;;
  *)
    echo "Usage: $0 --all | --is-esp32 DIR | --from-changes [path...]" >&2
    exit 1
    ;;
esac
