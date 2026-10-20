#!/usr/bin/env bash
# Fail when gofmt would change a .go file under the given directories.
#
# Skips vendor and testdata. Vendored files belong to upstream. Testdata
# holds fixtures that are often left unformatted on purpose, including
# analyzer inputs. git-k8s's check-gofmt skips the same trees.
#
# gofmt -l exits 0 even when it would reformat files, so this script
# fails when that listing is non-empty. A gofmt error, such as a file
# that does not parse, fails the script too.
#
# Usage: check-gofmt.sh DIR...
# Test:  bash .github/scripts/check-gofmt_test.sh
set -euo pipefail

if [ "$#" -eq 0 ]; then
  echo "usage: check-gofmt.sh DIR..." >&2
  exit 2
fi

if ! command -v gofmt >/dev/null 2>&1; then
  echo "gofmt: gofmt is not on PATH" >&2
  exit 2
fi

for dir in "$@"; do
  if [ ! -d "$dir" ]; then
    echo "gofmt: not a directory: ${dir}" >&2
    exit 2
  fi
done

files=()
while IFS= read -r -d '' file; do
  files+=("$file")
done < <(find "$@" -type f -name '*.go' \
  -not -path '*/vendor/*' \
  -not -path '*/testdata/*' \
  -print0)

if [ "${#files[@]}" -eq 0 ]; then
  exit 0
fi

failed=0
unformatted=()
batch=()

flush() {
  local out
  if [ "${#batch[@]}" -eq 0 ]; then
    return 0
  fi
  if ! out=$(gofmt -l "${batch[@]}"); then
    failed=1
  fi
  if [ -n "${out}" ]; then
    local line
    while IFS= read -r line; do
      if [ -n "$line" ]; then
        unformatted+=("$line")
      fi
    done <<< "${out}"
  fi
  batch=()
}

for file in "${files[@]}"; do
  batch+=("$file")
  if [ "${#batch[@]}" -ge 100 ]; then
    flush
  fi
done
flush

if [ "$failed" -ne 0 ]; then
  echo "gofmt failed. A file did not parse, or gofmt returned an error." >&2
  exit 1
fi

if [ "${#unformatted[@]}" -eq 0 ]; then
  exit 0
fi

echo "gofmt would reformat:"
printf '%s\n' "${unformatted[@]}"
echo
gofmt -d "${unformatted[@]}" || true
exit 1
