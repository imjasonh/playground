#!/usr/bin/env bash
# Tests for detect-ios-bootstrap-needed.sh. Run:
#   bash .github/scripts/detect-ios-bootstrap-needed_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
detect="$script_dir/detect-ios-bootstrap-needed.sh"
failures=0

assert_eq() {
  local want="$1"
  local got="$2"
  local name="$3"
  if [[ "$want" != "$got" ]]; then
    echo "FAIL: ${name}: want=${want} got=${got}" >&2
    failures=$((failures + 1))
  else
    echo "ok: ${name}"
  fi
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# Minimal fake repo: one iOS app with the files the detector cares about.
mkdir -p "$work/ios/fastlane" "$work/ios/Sources/Experiments/Foo" "$work/.github/scripts"
cp "$detect" "$work/.github/scripts/detect-ios-bootstrap-needed.sh"
chmod +x "$work/.github/scripts/detect-ios-bootstrap-needed.sh"

cat > "$work/ios/project.yml" <<'EOF'
name: Playground
targets:
  Playground:
    type: application
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground
    info:
      properties:
        NSCameraUsageDescription: camera
EOF

cat > "$work/ios/fastlane/Matchfile" <<'EOF'
app_identifier(["io.github.imjasonh.playground"])
EOF

cat > "$work/ios/fastlane/Fastfile" <<'EOF'
SIGNING_IDENTIFIERS = ["io.github.imjasonh.playground"]
lane :test do
  run_tests
end
lane :signing_bootstrap do
  ensure_bundle_ids!([{ id: "io.github.imjasonh.playground", name: "Playground" }])
end
EOF

echo '<?xml version="1.0"?><!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd"><plist version="1.0"><dict></dict></plist>' \
  > "$work/ios/Playground.entitlements"

cd "$work"
git init -q
git config user.email "test@example.com"
git config user.name "test"
git add .
git commit -q -m "base"
base=$(git rev-parse HEAD)

# 1) Ordinary experiment file → false
mkdir -p ios/Sources/Experiments/Foo
echo "struct Foo {}" > ios/Sources/Experiments/Foo/Foo.swift
git add ios/Sources/Experiments/Foo/Foo.swift
git commit -q -m "experiment"
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --diff "${base}...HEAD")
assert_eq "false" "$got" "experiment-only change"

# Reset to base for isolated cases
git reset -q --hard "$base"

# 2) Info.plist privacy string in project.yml → false
cat > ios/project.yml <<'EOF'
name: Playground
targets:
  Playground:
    type: application
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground
    info:
      properties:
        NSCameraUsageDescription: camera
        NSMicrophoneUsageDescription: mic
EOF
git add ios/project.yml
git commit -q -m "privacy string"
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --diff "${base}...HEAD")
assert_eq "false" "$got" "project.yml Info.plist-only change"

git reset -q --hard "$base"

# 3) New extension target / bundle id in project.yml → true
cat > ios/project.yml <<'EOF'
name: Playground
targets:
  Playground:
    type: application
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground
    info:
      properties:
        NSCameraUsageDescription: camera
  NewKeyboard:
    type: app-extension
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground.newkeyboard
EOF
git add ios/project.yml
git commit -q -m "new extension"
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --diff "${base}...HEAD")
assert_eq "true" "$got" "new app-extension target"

git reset -q --hard "$base"

# 4) New entitlement key in project.yml → true
cat > ios/project.yml <<'EOF'
name: Playground
targets:
  Playground:
    type: application
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground
        CODE_SIGN_ENTITLEMENTS: Playground.entitlements
    entitlements:
      path: Playground.entitlements
      properties:
        com.apple.developer.healthkit: true
    info:
      properties:
        NSCameraUsageDescription: camera
EOF
git add ios/project.yml
git commit -q -m "healthkit entitlement"
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --diff "${base}...HEAD")
assert_eq "true" "$got" "new com.apple.developer entitlement"

git reset -q --hard "$base"

# 5) Matchfile change → true
echo 'app_identifier(["io.github.imjasonh.playground","io.github.imjasonh.playground.kb"])' \
  > ios/fastlane/Matchfile
git add ios/fastlane/Matchfile
git commit -q -m "matchfile"
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --diff "${base}...HEAD")
assert_eq "true" "$got" "Matchfile change"

git reset -q --hard "$base"

# 6) Entitlements file change → true
echo '<?xml version="1.0"?><!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd"><plist version="1.0"><dict><key>com.apple.developer.healthkit</key><true/></dict></plist>' \
  > ios/Playground.entitlements
git add ios/Playground.entitlements
git commit -q -m "entitlements plist"
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --diff "${base}...HEAD")
assert_eq "true" "$got" "entitlements file change"

git reset -q --hard "$base"

# 7) Fastfile signing identifiers → true
cat > ios/fastlane/Fastfile <<'EOF'
SIGNING_IDENTIFIERS = [
  "io.github.imjasonh.playground",
  "io.github.imjasonh.playground.kb",
]
lane :test do
  run_tests
end
lane :signing_bootstrap do
  ensure_bundle_ids!([{ id: "io.github.imjasonh.playground", name: "Playground" }])
end
EOF
git add ios/fastlane/Fastfile
git commit -q -m "signing ids"
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --diff "${base}...HEAD")
assert_eq "true" "$got" "Fastfile SIGNING_IDENTIFIERS change"

git reset -q --hard "$base"

# 8) Fastfile unrelated test tweak → false
cat > ios/fastlane/Fastfile <<'EOF'
SIGNING_IDENTIFIERS = ["io.github.imjasonh.playground"]
lane :test do
  run_tests(number_of_retries: 3)
end
lane :signing_bootstrap do
  ensure_bundle_ids!([{ id: "io.github.imjasonh.playground", name: "Playground" }])
end
EOF
git add ios/fastlane/Fastfile
git commit -q -m "retry tweak"
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --diff "${base}...HEAD")
assert_eq "false" "$got" "Fastfile test-only change"

git reset -q --hard "$base"

# 9) --from-changes with DIFF_RANGE for privacy-only project.yml → false
cat > ios/project.yml <<'EOF'
name: Playground
targets:
  Playground:
    type: application
    settings:
      base:
        PRODUCT_BUNDLE_IDENTIFIER: io.github.imjasonh.playground
    info:
      properties:
        NSCameraUsageDescription: camera
        NSMicrophoneUsageDescription: mic
EOF
git add ios/project.yml
git commit -q -m "privacy via from-changes"
got=$(
  DIFF_RANGE="${base}...HEAD" \
    bash .github/scripts/detect-ios-bootstrap-needed.sh --from-changes ios/project.yml
)
assert_eq "false" "$got" "--from-changes + DIFF_RANGE privacy-only"

# 10) --from-changes without DIFF_RANGE on project.yml → true (conservative)
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --from-changes ios/project.yml)
assert_eq "true" "$got" "--from-changes without DIFF_RANGE is conservative"

# 11) Non-iOS path → false
got=$(bash .github/scripts/detect-ios-bootstrap-needed.sh --from-changes README.md kanoodle/index.html)
assert_eq "false" "$got" "non-iOS paths"

if ((failures > 0)); then
  echo "$failures test(s) failed." >&2
  exit 1
fi
echo "All detect-ios-bootstrap-needed tests passed."
