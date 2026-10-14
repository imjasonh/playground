#!/bin/sh
# Check the upload zip layout and the store listing images.
set -eu
cd "$(dirname "$0")"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
bash pack.sh "$tmp/duplicate-tabs.zip" >/dev/null
python3 - "$tmp/duplicate-tabs.zip" <<'PY'
import json, struct, sys, zipfile
from pathlib import Path

archive = zipfile.ZipFile(sys.argv[1])
names = sorted(archive.namelist())
expected = [
    "background.js",
    "controller.js",
    "duplicates.js",
    "icons/128.png",
    "icons/16.png",
    "icons/32.png",
    "icons/48.png",
    "manifest.json",
]
if names != expected:
    raise SystemExit(f"zip entries {names} != {expected}")
if any(name.endswith("/") or name.startswith("/") or name.startswith("store/") for name in names):
    raise SystemExit("zip must be a flat package, not a directory or a listing image")
manifest = json.loads(archive.read("manifest.json"))
if manifest["manifest_version"] != 3:
    raise SystemExit("manifest_version must be 3")
if manifest["version"] != "0.1.0":
    raise SystemExit("version must be 0.1.0")
if manifest["name"] != "Close Duplicate Tabs":
    raise SystemExit("name must be Close Duplicate Tabs")
description = manifest["description"]
if len(description) > 132 or "badge" not in description or "URL" not in description:
    raise SystemExit(f"manifest description is {len(description)} characters and must name the badge and the URL")
if manifest.get("permissions") != ["tabs"]:
    raise SystemExit(f"permissions must be exactly tabs, got {manifest.get('permissions')}")
if "host_permissions" in manifest or "content_scripts" in manifest or "optional_permissions" in manifest:
    raise SystemExit("package must not declare host permissions or content scripts")
action = manifest["action"]
if "default_popup" in action:
    raise SystemExit("a popup would swallow the toolbar click")
background = manifest["background"]
if background.get("service_worker") != "background.js" or background.get("type") != "module":
    raise SystemExit("service worker must be background.js as a module")
source = archive.read("background.js").decode()
if "start(chrome)" not in source or "onClicked" in source:
    raise SystemExit("background.js must start the controller and leave the click handler there")

def png_info(blob):
    if blob[:8] != b"\x89PNG\r\n\x1a\n":
        raise SystemExit("not a png")
    width, height, bit_depth, color = struct.unpack(">IIBB", blob[16:26])
    return width, height, bit_depth, color

for size in (16, 32, 48, 128):
    width, height, _, _ = png_info(archive.read(f"icons/{size}.png"))
    if (width, height) != (size, size):
        raise SystemExit(f"icons/{size}.png is {width}x{height}")

icon = Path("store/icon-128.png").read_bytes()
width, height, bit_depth, color = png_info(icon)
if (width, height, bit_depth, color) != (128, 128, 8, 6):
    raise SystemExit(
        f"store icon is {width}x{height} depth {bit_depth} color {color}, want 128x128 8-bit RGBA"
    )

shot = Path("store/screenshot.png").read_bytes()
width, height, bit_depth, color = png_info(shot)
if (width, height, bit_depth, color) != (1280, 800, 8, 2):
    raise SystemExit(
        f"screenshot is {width}x{height} depth {bit_depth} color {color}, want 1280x800 24-bit RGB"
    )
print("ok")
PY
