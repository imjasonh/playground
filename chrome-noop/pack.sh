#!/bin/sh
# Build a Chrome Web Store upload zip. manifest.json is at the archive root.
set -eu
cd "$(dirname "$0")"
out="${1:-chrome-noop.zip}"
rm -f "$out"
zip -q -X -D -r "$out" manifest.json popup.html popup.css icons
echo "$out"
