#!/usr/bin/env bash
# Runs on the tenant's runner through Bazel's test wrapper, which needs bash
# on the runner, and checks that the test can read its data dependency.
set -euo pipefail
f="${TEST_SRCDIR}/_main/whoami.txt"
[[ "$(wc -l <"${f}")" -eq 2 ]] || { echo "unexpected ${f}:"; cat "${f}"; exit 1; }
