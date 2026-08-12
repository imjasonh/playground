#!/usr/bin/env bash
# Arch trampoline for CNB bin/detect and bin/build.
# package.sh installs this as bin/detect and bin/build, with real binaries at
# bin/<amd64|arm64>/{detect,build}. That lets a single buildpack directory be
# copied into every platform of a multi-arch builder — each build container
# execs the matching native binary.
set -euo pipefail

dir="$(cd "$(dirname "$0")" && pwd)"
cmd="$(basename "$0")"

case "$(uname -m)" in
  x86_64 | amd64) arch=amd64 ;;
  aarch64 | arm64) arch=arm64 ;;
  *)
    echo "playground/go: unsupported build-container arch: $(uname -m)" >&2
    exit 1
    ;;
esac

bin="${dir}/${arch}/${cmd}"
if [[ ! -x "$bin" ]]; then
  echo "playground/go: missing ${arch}/${cmd} — run scripts/package.sh" >&2
  exit 1
fi
exec "$bin" "$@"
