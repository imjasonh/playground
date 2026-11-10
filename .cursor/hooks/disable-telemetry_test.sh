#!/usr/bin/env bash
# Tests disable-telemetry.sh. Run with:
#   bash .cursor/hooks/disable-telemetry_test.sh
set -euo pipefail

hook="$(dirname "${BASH_SOURCE[0]}")/disable-telemetry.sh"
failures=0

check() {
  local name=$1 input=$2 want=$3 got
  got=$(bash "$hook" <<<"$input")
  if [[ "$got" != "$want" ]]; then
    echo "FAIL $name"
    echo "  got:  $got"
    echo "  want: $want"
    failures=$((failures + 1))
  fi
}

check "other command" \
  '{"tool_name":"Shell","tool_input":{"command":"npm test"}}' \
  '{"permission":"allow"}'

check "cli command" \
  '{"tool_name":"Shell","tool_input":{"command":"npx -y modern-web-guidance@latest search \"x\"","working_directory":"/repo"}}' \
  '{"permission":"allow","updated_input":{"command":"export DISABLE_TELEMETRY=1; npx -y modern-web-guidance@latest search \"x\"","working_directory":"/repo"}}'

check "already disabled" \
  '{"tool_name":"Shell","tool_input":{"command":"DISABLE_TELEMETRY=1 npx -y modern-web-guidance@latest list"}}' \
  '{"permission":"allow"}'

if ((failures > 0)); then
  exit 1
fi
echo PASS
