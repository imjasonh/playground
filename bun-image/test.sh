#!/usr/bin/env bash
# Smoke-test bun-image: compile example.js, run it on the host, and (if crane
# is available) pack a local image tarball and check its config.
set -euo pipefail

cd "$(dirname "$0")"

if ! command -v bun >/dev/null 2>&1; then
  echo "need bun on PATH" >&2
  exit 1
fi

host_arch="$(uname -m)"
case "$host_arch" in
  x86_64 | amd64) target="bun-linux-x64" ;;
  aarch64 | arm64) target="bun-linux-arm64" ;;
  *)
    echo "unsupported host architecture: ${host_arch}" >&2
    exit 1
    ;;
esac

out=""
server_pid=""
cleanup() {
  if [[ -n "$server_pid" ]]; then
    kill "$server_pid" 2>/dev/null || true
  fi
  if [[ -n "$out" ]]; then
    rm -f "$out"
  fi
}
trap cleanup EXIT

echo "compiling example.js (${target})"
rm -f ./example
bun build --compile --minify --target="$target" ./example.js --outfile=example >&2

if [[ ! -x ./example ]]; then
  echo "bun compile did not write an executable ./example" >&2
  exit 1
fi

if ! file ./example | grep -q 'ELF'; then
  echo "expected an ELF executable, got: $(file ./example)" >&2
  exit 1
fi

hello="$(./example --hello)"
if [[ "$hello" != "bun-image-ok" ]]; then
  echo "expected bun-image-ok from ./example --hello, got: ${hello}" >&2
  exit 1
fi
echo "ok --hello"

port=18765
PORT="$port" ./example &
server_pid=$!

body=""
i=0
while [[ "$i" -lt 20 ]]; do
  if body="$(curl -fsS "http://127.0.0.1:${port}/" 2>/dev/null)"; then
    break
  fi
  i=$((i + 1))
  sleep 0.1
done
kill "$server_pid" 2>/dev/null || true
server_pid=""

if [[ "$body" != "Hello world" ]]; then
  echo "expected Hello world from http://127.0.0.1:${port}/, got: ${body}" >&2
  exit 1
fi
echo "ok http"

if ! command -v crane >/dev/null 2>&1; then
  echo "skip image pack (crane not on PATH)"
  echo "all ok"
  exit 0
fi

out="$(mktemp)"

echo "pack local tarball"
BUN_IMAGE_OUT="$out" ./build.sh bun-image.local/example >/dev/null

python3 - "$out" <<'PY'
import json
import sys
import tarfile

path = sys.argv[1]
with tarfile.open(path) as tf:
    manifest = json.load(tf.extractfile("manifest.json"))
    cfg_name = manifest[0]["Config"]
    cfg = json.load(tf.extractfile(cfg_name))
config = cfg.get("config", cfg)
entrypoint = config.get("Entrypoint")
if entrypoint != ["/example"]:
    sys.exit(f"entrypoint {entrypoint!r}, want ['/example']")
ports = config.get("ExposedPorts") or {}
if "8000" not in ports and "8000/tcp" not in ports:
    sys.exit(f"ExposedPorts {ports!r}, want 8000")
print("ok image config", manifest[0].get("RepoTags"), entrypoint)
PY

echo "all ok"
