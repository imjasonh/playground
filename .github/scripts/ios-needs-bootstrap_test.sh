#!/usr/bin/env bash
# Tests for ios-needs-bootstrap.sh.
# Run: bash .github/scripts/ios-needs-bootstrap_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
detect="$script_dir/ios-needs-bootstrap.sh"

failures=0
assert_eq() {
  local got="$1" want="$2" label="$3"
  if [[ "$got" != "$want" ]]; then
    echo "FAIL: $label" >&2
    echo "  got:  $got" >&2
    echo "  want: $want" >&2
    failures=$((failures + 1))
  fi
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

git -C "$work" init -q
git -C "$work" config user.email "test@example.com"
git -C "$work" config user.name "test"
mkdir -p "$work/ios/fastlane" "$work/hello-macos"

write_project_yml() {
  cat > "$work/ios/project.yml" <<'EOF'
name: Playground
targets:
  Playground:
    type: application
    platform: iOS
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground
        CODE_SIGN_ENTITLEMENTS: Playground.entitlements
    entitlements:
      path: Playground.entitlements
EOF
}

write_project_yml

cat > "$work/ios/Playground.entitlements" <<'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict/>
</plist>
EOF

cat > "$work/ios/fastlane/Fastfile" <<'EOF'
lane :test do
end
EOF

cat > "$work/ios/fastlane/Matchfile" <<'EOF'
git_url("example")
EOF

cat > "$work/hello-macos/Hello.entitlements" <<'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict/>
</plist>
EOF

(
  cd "$work"
  git add -A
  git commit -qm base

  mkdir -p ios/Sources/Experiments/Demo
  echo '// demo' > ios/Sources/Experiments/Demo/Demo.swift
  git add -A
  git commit -qm experiment
  assert_eq "$(bash "$detect" HEAD~1...HEAD)" "false" "experiment sources"

  cat >> ios/project.yml <<'EOF'
  ArmyListStress:
    type: tool
    platform: macOS
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground.army-list-stress
EOF
  git add -A
  git commit -qm 'macos cli tool'
  assert_eq "$(bash "$detect" HEAD~1...HEAD)" "false" "macos tool PRODUCT_BUNDLE_IDENTIFIER"

  write_project_yml
  cat > ios/project.yml <<'EOF'
name: Playground
targets:
  Playground:
    type: application
    platform: iOS
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground
        CODE_SIGN_ENTITLEMENTS: Playground.entitlements
        com.apple.developer.nfc.readersession.formats: [TAG]
    entitlements:
      path: Playground.entitlements
EOF
  git add -A
  git commit -qm 'host capability'
  assert_eq "$(bash "$detect" HEAD~1...HEAD)" "true" "project.yml com.apple.developer"

  cat > ios/Playground.entitlements <<'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>com.apple.developer.healthkit</key>
  <true/>
</dict>
</plist>
EOF
  git add -A
  git commit -qm entitlements
  assert_eq "$(bash "$detect" HEAD~1...HEAD)" "true" "ios entitlements file"

  cat >> ios/project.yml <<'EOF'
  NewKeyboard:
    type: app-extension
    platform: iOS
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground.newkeyboard
EOF
  git add -A
  git commit -qm extension
  assert_eq "$(bash "$detect" HEAD~1...HEAD)" "true" "type: app-extension"

  echo '<!-- tweak -->' >> hello-macos/Hello.entitlements
  git add -A
  git commit -qm 'macos app entitlements'
  assert_eq "$(bash "$detect" HEAD~1...HEAD)" "false" "non-ios entitlements ignored"
)

if [[ "$failures" -ne 0 ]]; then
  echo "$failures failure(s)" >&2
  exit 1
fi
echo "ok"
