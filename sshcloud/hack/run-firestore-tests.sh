#!/usr/bin/env bash
# Run store + placement Firestore tests against a local emulator.
# Usage: bash hack/run-firestore-tests.sh
set -euo pipefail
cd "$(dirname "$0")/.."

PROJECT="${FIRESTORE_PROJECT_ID:-sshcloud-test}"
HOST="${FIRESTORE_EMULATOR_HOST:-}"

cleanup() {
  if [[ -n "${EMULATOR_PID:-}" ]] && kill -0 "$EMULATOR_PID" 2>/dev/null; then
    kill "$EMULATOR_PID" 2>/dev/null || true
    wait "$EMULATOR_PID" 2>/dev/null || true
  fi
}
trap cleanup EXIT

if [[ -z "$HOST" ]]; then
  echo "starting Firestore emulator on 127.0.0.1:8080…"
  npx --yes firebase-tools@13.29.1 emulators:start --only firestore --project "$PROJECT" \
    >/tmp/sshcloud-firestore-emulator.log 2>&1 &
  EMULATOR_PID=$!
  for i in $(seq 1 60); do
    if grep -q "All emulators ready" /tmp/sshcloud-firestore-emulator.log 2>/dev/null; then
      break
    fi
    if ! kill -0 "$EMULATOR_PID" 2>/dev/null; then
      echo "emulator failed to start; log:" >&2
      cat /tmp/sshcloud-firestore-emulator.log >&2 || true
      exit 1
    fi
    sleep 1
  done
  if ! grep -q "All emulators ready" /tmp/sshcloud-firestore-emulator.log 2>/dev/null; then
    echo "timed out waiting for emulator" >&2
    cat /tmp/sshcloud-firestore-emulator.log >&2 || true
    exit 1
  fi
  export FIRESTORE_EMULATOR_HOST=127.0.0.1:8080
fi

export FIRESTORE_PROJECT_ID="$PROJECT"
export GOTOOLCHAIN="${GOTOOLCHAIN:-auto}"
go test ./internal/store/ ./internal/placement/ -count=1 -run 'Firestore'
echo "Firestore tests passed"
