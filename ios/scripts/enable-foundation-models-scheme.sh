#!/usr/bin/env bash
# After `xcodegen generate`, force Simulated Foundation Models Availability to
# Apple Intelligence Enabled on the Playground scheme (Run + Test).
#
# Same control as Xcode → Edit Scheme → Run/Test → Options →
# Simulated Foundation Models Availability → Apple Intelligence Enabled.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
scheme="${root}/Playground.xcodeproj/xcshareddata/xcschemes/Playground.xcscheme"

if [[ ! -f "$scheme" ]]; then
  echo "error: missing scheme at $scheme (run xcodegen generate first)" >&2
  exit 1
fi

ATTR='simulatedFoundationModelsAvailability'
VALUE='AppleIntelligenceEnabled'

python3 - "$scheme" "$ATTR" "$VALUE" <<'PY'
import sys
import xml.etree.ElementTree as ET

path, attr, value = sys.argv[1], sys.argv[2], sys.argv[3]
# Preserve the original XML declaration / formatting as much as ElementTree allows.
tree = ET.parse(path)
root = tree.getroot()
updated = []
for tag in ("LaunchAction", "TestAction"):
    for node in root.iter(tag):
        node.set(attr, value)
        updated.append(tag)

if not updated:
    raise SystemExit(f"error: no LaunchAction/TestAction in {path}")

tree.write(path, encoding="UTF-8", xml_declaration=True)
print(f"Set {attr}={value} on: {', '.join(updated)}")
print(f"Patched {path}")
PY
