#!/usr/bin/env bash
# Install or update Xeneon Cursor from the latest xeneon-cursor-v* GitHub Release.
set -euo pipefail

REPO="${XENEON_GITHUB_REPO:-imjasonh/playground}"
ASSET_NAME="XeneonCursor-macos.zip"
INSTALL_DIR="${XENEON_INSTALL_DIR:-$HOME/Applications}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

echo "Fetching latest Xeneon Cursor release from ${REPO}…"
API="https://api.github.com/repos/${REPO}/releases?per_page=30"
JSON="$(curl -fsSL -H 'Accept: application/vnd.github+json' -H 'User-Agent: XeneonCursor-Installer' "$API")"

read -r TAG URL < <(
  printf '%s' "$JSON" | ASSET_NAME="$ASSET_NAME" python3 -c '
import json, os, sys
data = json.load(sys.stdin)
name = os.environ["ASSET_NAME"]
for release in data:
    tag = release.get("tag_name") or ""
    if not tag.startswith("xeneon-cursor-v"):
        continue
    for asset in release.get("assets") or []:
        if asset.get("name") == name and asset.get("browser_download_url"):
            print(tag, asset["browser_download_url"])
            sys.exit(0)
raise SystemExit("No xeneon-cursor-v* release with " + name + " found")
'
)

echo "Latest: ${TAG}"
echo "Downloading ${URL}"
curl -fL --progress-bar -o "$TMP/$ASSET_NAME" "$URL"

echo "Unpacking…"
mkdir -p "$TMP/unpacked"
ditto -x -k "$TMP/$ASSET_NAME" "$TMP/unpacked"
mkdir -p "$INSTALL_DIR"
rm -rf "$INSTALL_DIR/XeneonCursor.app"
ditto "$TMP/unpacked/XeneonCursor.app" "$INSTALL_DIR/XeneonCursor.app"

if command -v xattr >/dev/null 2>&1; then
  xattr -dr com.apple.quarantine "$INSTALL_DIR/XeneonCursor.app" 2>/dev/null || true
fi

echo "Installed to $INSTALL_DIR/XeneonCursor.app"
echo "Launch with: open \"$INSTALL_DIR/XeneonCursor.app\""
echo
echo "Touch tip: macOS needs a community HID helper for the XENEON EDGE touchscreen."
echo "See xeneon-cursor/README.md for links."
