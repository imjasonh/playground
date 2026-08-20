#!/usr/bin/env bash
# Run the posts catalog unit tests (discovery, Markdown, git dates, assets).
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"

echo "::group::build-blog tests"
python3 .github/scripts/build-blog_test.py
echo "::endgroup::"
