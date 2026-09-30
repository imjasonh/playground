#!/bin/sh
# Check the upload zip layout and the store screenshot dimensions.
set -eu
cd "$(dirname "$0")"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
bash pack.sh "$tmp/chrome-noop.zip" >/dev/null
python3 - "$tmp/chrome-noop.zip" <<'PY'
import json, struct, sys, zipfile
from pathlib import Path

archive = zipfile.ZipFile(sys.argv[1])
names = sorted(archive.namelist())
expected = [
    "icons/128.png",
    "icons/16.png",
    "icons/32.png",
    "icons/48.png",
    "manifest.json",
    "popup.css",
    "popup.html",
]
if names != expected:
    raise SystemExit(f"zip entries {names} != {expected}")
if any(name.endswith("/") or name.startswith("/") for name in names):
    raise SystemExit("zip must be a flat package, not a directory")
manifest = json.loads(archive.read("manifest.json"))
if manifest["manifest_version"] != 3:
    raise SystemExit("manifest_version must be 3")
if manifest["version"] != "0.0.1":
    raise SystemExit("version must be 0.0.1")
if "permissions" in manifest or "host_permissions" in manifest:
    raise SystemExit("no-op package must not declare permissions")

def png_info(blob):
    if blob[:8] != b"\x89PNG\r\n\x1a\n":
        raise SystemExit("not a png")
    width, height, bit_depth, color = struct.unpack(">IIBB", blob[16:26])
    return width, height, bit_depth, color

for size in (16, 32, 48, 128):
    width, height, _, _ = png_info(archive.read(f"icons/{size}.png"))
    if (width, height) != (size, size):
        raise SystemExit(f"icons/{size}.png is {width}x{height}")

shot = Path("store/screenshot.png").read_bytes()
width, height, bit_depth, color = png_info(shot)
if (width, height, bit_depth, color) != (1280, 800, 8, 2):
    raise SystemExit(
        f"screenshot is {width}x{height} depth {bit_depth} color {color}, want 1280x800 24-bit RGB"
    )
print("ok")
PY
