#!/usr/bin/env bash
set -euo pipefail
f="${TEST_SRCDIR}/_main/small.txt"
[[ "$(wc -l <"${f}")" -eq 3 ]] || { echo "unexpected ${f}:"; cat "${f}"; exit 1; }
