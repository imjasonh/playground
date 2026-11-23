#!/usr/bin/env bash
# Tests for .github/scripts/discover-godot-apps.sh.
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd "$script_dir/../.." && pwd)
cd "$repo_root"

got_all=$(bash .github/scripts/discover-godot-apps.sh --all)
if ! jq -e 'index("one-tap-quest") != null' <<<"$got_all" >/dev/null; then
  echo "FAIL: expected one-tap-quest in --all output, got $got_all" >&2
  exit 1
fi

got_hit=$(printf 'one-tap-quest/scripts/main.gd\nREADME.md\n' | bash .github/scripts/discover-godot-apps.sh --from-changes)
if [ "$got_hit" != '["one-tap-quest"]' ]; then
  echo "FAIL: expected [\"one-tap-quest\"], got $got_hit" >&2
  exit 1
fi

got_miss=$(printf 'README.md\nhello/index.html\n' | bash .github/scripts/discover-godot-apps.sh --from-changes)
if [ "$got_miss" != '[]' ]; then
  echo "FAIL: expected [], got $got_miss" >&2
  exit 1
fi

echo "ok - discover-godot-apps.sh"
