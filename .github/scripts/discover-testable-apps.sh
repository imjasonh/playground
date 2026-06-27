#!/usr/bin/env bash
# Emit a JSON array of top-level app directories that define an npm test script.
# An app is a directory with index.html (same rule as deploy/preview workflows).
set -euo pipefail

apps=()

for dir in */; do
  name="${dir%/}"

  # Skip hidden directories (e.g. .github)
  if [[ "$name" == .* ]]; then
    continue
  fi

  if [[ ! -f "$name/index.html" ]]; then
    continue
  fi

  if [[ ! -f "$name/package.json" ]]; then
    continue
  fi

  if node -e "
    const pkg = require('./${name}/package.json');
    process.exit(pkg.scripts && pkg.scripts.test ? 0 : 1);
  " 2>/dev/null; then
    apps+=("$name")
  fi
done

if ((${#apps[@]} == 0)); then
  echo '[]'
else
  printf '%s\n' "${apps[@]}" | jq -R . | jq -cs .
fi
