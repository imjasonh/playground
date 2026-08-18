#!/usr/bin/env bash
# Tests for check-worker-observability.py.
# Run: bash .github/scripts/check-worker-observability_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
check="$script_dir/check-worker-observability.py"

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

assert_exit() {
  local want="$1" label="$2"
  shift 2
  local got=0
  "$@" >/dev/null 2>&1 || got=$?
  assert_eq "$got" "$want" "$label"
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

cat > "$work/ok.toml" <<'EOF'
name = "ok"
[observability]
enabled = true
[observability.logs]
enabled = true
invocation_logs = true
[observability.traces]
enabled = true
EOF

cat > "$work/logs-implied.toml" <<'EOF'
name = "implied"
[observability]
enabled = true
[observability.traces]
enabled = true
EOF

cat > "$work/missing.toml" <<'EOF'
name = "missing"
EOF

cat > "$work/no-traces.toml" <<'EOF'
name = "no-traces"
[observability]
enabled = true
EOF

cat > "$work/traces-off.toml" <<'EOF'
name = "traces-off"
[observability]
enabled = true
[observability.traces]
enabled = false
EOF

cat > "$work/invocation-off.toml" <<'EOF'
name = "invocation-off"
[observability]
enabled = true
[observability.logs]
invocation_logs = false
[observability.traces]
enabled = true
EOF

assert_exit 0 "full observability block" python3 "$check" "$work/ok.toml"
assert_exit 0 "top-level logs imply invocation logs" python3 "$check" "$work/logs-implied.toml"
assert_exit 1 "missing observability" python3 "$check" "$work/missing.toml"
assert_exit 1 "logs without traces" python3 "$check" "$work/no-traces.toml"
assert_exit 1 "traces disabled" python3 "$check" "$work/traces-off.toml"
assert_exit 1 "invocation logs disabled" python3 "$check" "$work/invocation-off.toml"

# Live repo: every current Worker app must already satisfy the default.
assert_exit 0 "repo --all" python3 "$check" --all

# --all walks $repo_root (script parents), not $PWD.
(
  cd "$work"
  assert_exit 0 "--all ignores cwd" python3 "$check" --all
)

if ((failures > 0)); then
  echo "$failures failure(s)" >&2
  exit 1
fi
echo "ok"
