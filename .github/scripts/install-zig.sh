#!/usr/bin/env bash
# Install Zig 0.17.0 for Linux x86_64 and print the directory that contains it.
#
# Stdout is only that directory. deploy-gcp.sh prepends it to PATH, so
# the checksum check writes to stderr.
#
# The checksum is the x86_64-linux entry for 0.17.0 in
# https://ziglang.org/download/index.json. If `zig version` is already
# 0.17.0, this prints that binary's directory and does not download.
#
#   install-zig.sh --version
set -euo pipefail

ZIG_VERSION=0.17.0
ZIG_SHA256=1cbe9df9f27e6b78d14ccbca43b6703a404ef79ef1c463de901d7f088d4e2026
ZIG_TARGET=x86_64-linux
ZIG_NAME="zig-${ZIG_TARGET}-${ZIG_VERSION}"
ZIG_URL="https://ziglang.org/download/${ZIG_VERSION}/${ZIG_NAME}.tar.xz"

if [[ "${1:-}" == "--version" ]]; then
  echo "$ZIG_VERSION"
  exit 0
fi

if command -v zig >/dev/null 2>&1 && [[ "$(zig version)" == "$ZIG_VERSION" ]]; then
  dirname "$(command -v zig)"
  exit 0
fi

if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
  echo "install-zig: this download is Linux x86_64. Install zig ${ZIG_VERSION} and re-run." >&2
  exit 1
fi

prefix="${ZIG_PREFIX:-${HOME}/.cache/zig/${ZIG_NAME}}"
if [[ ! -x "${prefix}/zig" ]]; then
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  curl -fsSL --retry 3 -o "${tmp}/zig.tar.xz" "$ZIG_URL"
  echo "${ZIG_SHA256}  ${tmp}/zig.tar.xz" | sha256sum -c - >&2
  tar -xJf "${tmp}/zig.tar.xz" -C "$tmp"
  mkdir -p "$(dirname "$prefix")"
  rm -rf "$prefix"
  mv "${tmp}/${ZIG_NAME}" "$prefix"
  trap - EXIT
  rm -rf "$tmp"
fi

echo "$prefix"
