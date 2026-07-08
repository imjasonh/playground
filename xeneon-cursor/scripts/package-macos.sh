#!/usr/bin/env bash
# Build XeneonCursor.app and zip it for distribution.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VERSION="${1:-$(tr -d '[:space:]' < "$ROOT/VERSION")}"
DIST="$ROOT/dist"
APP="$DIST/XeneonCursor.app"
BIN_DIR="$DIST/bin"

echo "Building Xeneon Cursor v${VERSION}…"
rm -rf "$DIST"
mkdir -p "$BIN_DIR" "$APP/Contents/MacOS" "$APP/Contents/Resources/ui"

# Compile the Swift executable (requires macOS + Swift toolchain).
(
  cd "$ROOT/macos"
  swift build -c release --product XeneonCursor
)

BIN="$(cd "$ROOT/macos" && swift build -c release --show-bin-path)/XeneonCursor"
cp "$BIN" "$APP/Contents/MacOS/XeneonCursor"
chmod +x "$APP/Contents/MacOS/XeneonCursor"

# Info.plist with version substitution
sed "s/VERSION_PLACEHOLDER/${VERSION}/g" \
  "$ROOT/macos/Resources/Info.plist" > "$APP/Contents/Info.plist"

# Bundle UI + bridge
cp -R "$ROOT/ui/." "$APP/Contents/Resources/ui/"
cp "$ROOT/macos/Sources/XeneonCursor/Bridge.js" "$APP/Contents/Resources/Bridge.js"
echo -n "APPL????" > "$APP/Contents/PkgInfo"

# Ad-hoc sign so Gatekeeper is slightly happier on local installs.
if command -v codesign >/dev/null 2>&1; then
  codesign --force --deep --sign - "$APP" || true
fi

(
  cd "$DIST"
  ditto -c -k --sequesterRsrc --keepParent XeneonCursor.app "XeneonCursor-macos.zip"
)

cat > "$DIST/SHA256SUMS" <<EOF
$(shasum -a 256 "$DIST/XeneonCursor-macos.zip" | awk '{print $1}')  XeneonCursor-macos.zip
EOF

echo "Built:"
echo "  $APP"
echo "  $DIST/XeneonCursor-macos.zip"
echo "  $DIST/SHA256SUMS"
