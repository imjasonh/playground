#!/usr/bin/env bash
# Run the Pages home-page index unit tests (renderer + discovery).
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

echo "::group::render-index tests"
python3 .github/scripts/render-index_test.py
echo "::endgroup::"

echo "::group::discover-index tests"
bash .github/scripts/discover-index_test.sh
echo "::endgroup::"
