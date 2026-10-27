#!/bin/sh
# Build a Chrome Web Store upload zip. manifest.json is at the archive root.
set -eu
cd "$(dirname "$0")"
out="${1:-chrome-extension.zip}"
rm -f "$out"
zip -q -X -D -r "$out" manifest.json background.js controller.js duplicates.js base64.js selection.js clipboard.js offscreen.js offscreen.html icons
echo "$out"
