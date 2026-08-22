#!/usr/bin/env bash
# Smoke-test discover-exe-apps.sh against the live tree and a temp fixture.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

apps=$(bash .github/scripts/discover-exe-apps.sh --all)
echo "discover-exe-apps --all => ${apps}"
echo "$apps" | jq -e 'type == "array"' >/dev/null
echo "$apps" | jq -e 'index("chessh") != null' >/dev/null

from_changes=$(printf 'chessh/main.go\nREADME.md\n' | bash .github/scripts/discover-exe-apps.sh --from-changes)
echo "from-changes chessh/main.go => ${from_changes}"
echo "$from_changes" | jq -e '. == ["chessh"]' >/dev/null

none=$(printf 'README.md\n' | bash .github/scripts/discover-exe-apps.sh --from-changes)
echo "from-changes README.md => ${none}"
echo "$none" | jq -e '. == []' >/dev/null

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/fake-exe/iac" "$tmp/not-exe/iac"
cat >"$tmp/fake-exe/iac/providers.tf" <<'EOF'
terraform {
  required_providers {
    exedev = { source = "benjamin-lykins/exedev" }
  }
}
EOF
echo '# no exedev' >"$tmp/not-exe/iac/main.tf"

(
  cd "$tmp"
  got=$(bash "$repo_root/.github/scripts/discover-exe-apps.sh" --all)
  echo "fixture --all => ${got}"
  echo "$got" | jq -e '. == ["fake-exe"]' >/dev/null
)

echo "discover-exe-apps_test.sh: ok"
