#!/usr/bin/env bash
# Fetch the container2wasm/QEMU-Wasm emulator assets into this directory.
#
# The emulator is tens of megabytes of generated wasm, so it is not in git.
# It is produced by .github/workflows/container-runtime.yml, which uploads a
# "container-runtime-aarch64" artifact. Point this script at that artifact (a
# zip) or at any directory containing the c2w --to-js output.
#
#   ios/ContainerRuntime/fetch-runtime.sh --from-zip ~/Downloads/container-runtime-aarch64.zip
#   ios/ContainerRuntime/fetch-runtime.sh --from-dir /tmp/out-js/htdocs
#   ios/ContainerRuntime/fetch-runtime.sh --from-run 1234567890   # needs gh
#
# Without these files the app still builds and runs; Container Lab reports the
# runtime as missing and only the pull/inspect half works.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# The wasm and its packaged guest are named for the emulated machine
# (qemu-system-aarch64.wasm/.data), so check for the glue by name and the wasm
# by glob.
required=(out.js load.js arg-module.js)

usage() {
  sed -n '2,14p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
  exit "${1:-1}"
}

install_from_dir() {
  local source="$1"
  local missing=()
  for file in "${required[@]}"; do
    [ -f "$source/$file" ] || missing+=("$file")
  done
  compgen -G "$source/*.wasm" >/dev/null || missing+=("*.wasm")
  if [ "${#missing[@]}" -ne 0 ]; then
    echo "error: $source is missing: ${missing[*]}" >&2
    exit 1
  fi

  # Copy everything the build produced (there are worker/data side files whose
  # names depend on the emscripten version), but never clobber what git owns.
  for path in "$source"/*; do
    local name
    name="$(basename "$path")"
    case "$name" in
      index.html|vendor|fetch-runtime.sh|README.md|.gitignore) continue ;;
    esac
    cp -R "$path" "$here/$name"
  done

  echo "Installed into $here:"
  ls -lh "$here" | sed 1d
}

case "${1:-}" in
  --from-dir)
    [ $# -eq 2 ] || usage
    install_from_dir "$2"
    ;;
  --from-zip)
    [ $# -eq 2 ] || usage
    tmp="$(mktemp -d)"
    trap 'rm -rf "$tmp"' EXIT
    unzip -q "$2" -d "$tmp"
    # The artifact may contain the htdocs directory or its contents.
    if [ -d "$tmp/htdocs" ]; then
      install_from_dir "$tmp/htdocs"
    else
      install_from_dir "$tmp"
    fi
    ;;
  --from-run)
    [ $# -eq 2 ] || usage
    command -v gh >/dev/null || { echo "error: gh is required for --from-run" >&2; exit 1; }
    tmp="$(mktemp -d)"
    trap 'rm -rf "$tmp"' EXIT
    gh run download "$2" --name container-runtime-aarch64 --dir "$tmp"
    if [ -d "$tmp/htdocs" ]; then
      install_from_dir "$tmp/htdocs"
    else
      install_from_dir "$tmp"
    fi
    ;;
  -h|--help)
    usage 0
    ;;
  *)
    usage
    ;;
esac
