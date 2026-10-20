#!/usr/bin/env bash
# Tests for check-gofmt.sh.
# Run: bash .github/scripts/check-gofmt_test.sh
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
script="${script_dir}/check-gofmt.sh"

failures=0
fail() {
  echo "FAIL: $1" >&2
  failures=$((failures + 1))
}

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

formatted='package p

func F() {}
'
dirty='package p
func  F() {
}
'

mkdir -p "${work}/clean"
printf '%s' "$formatted" > "${work}/clean/a.go"
if ! bash "$script" "${work}/clean"; then
  fail "formatted tree should pass"
fi

mkdir -p "${work}/dirty"
printf '%s' "$dirty" > "${work}/dirty/a.go"
status=0
out=$(bash "$script" "${work}/dirty" 2>&1) || status=$?
if [ "$status" -eq 0 ]; then
  fail "unformatted tree should fail"
elif [ "$status" -ne 1 ]; then
  fail "unformatted tree should exit 1, got ${status}"
fi
if [[ "$out" != *"${work}/dirty/a.go"* ]]; then
  fail "unformatted failure should name the file, got: ${out}"
fi

mkdir -p "${work}/skip/testdata" "${work}/skip/vendor/x" "${work}/skip/pkg"
printf '%s' "$dirty" > "${work}/skip/testdata/a.go"
printf '%s' "$dirty" > "${work}/skip/vendor/x/a.go"
printf '%s' "$formatted" > "${work}/skip/pkg/ok.go"
# A name that merely contains those words is still checked.
printf '%s' "$formatted" > "${work}/skip/vendor.go"
if ! bash "$script" "${work}/skip"; then
  fail "vendor and testdata trees should be skipped"
fi

mkdir -p "${work}/skip-dirty/pkg"
printf '%s' "$dirty" > "${work}/skip-dirty/vendor.go"
status=0
bash "$script" "${work}/skip-dirty" >/dev/null 2>&1 || status=$?
if [ "$status" -eq 0 ]; then
  fail "vendor.go outside a vendor directory should be checked"
fi

mkdir -p "${work}/space dir"
printf '%s' "$dirty" > "${work}/space dir/a.go"
status=0
out=$(bash "$script" "${work}/space dir" 2>&1) || status=$?
if [ "$status" -ne 1 ] || [[ "$out" != *"space dir/a.go"* ]]; then
  fail "paths with spaces should fail and be named, status=${status} out=${out}"
fi

mkdir -p "${work}/bad"
printf 'package p\nfunc (\n' > "${work}/bad/a.go"
status=0
bash "$script" "${work}/bad" >/dev/null 2>&1 || status=$?
if [ "$status" -eq 0 ]; then
  fail "a file that does not parse should fail"
fi

mkdir -p "${work}/empty"
if ! bash "$script" "${work}/empty"; then
  fail "a directory with no Go files should pass"
fi

status=0
bash "$script" >/dev/null 2>&1 || status=$?
if [ "$status" -ne 2 ]; then
  fail "no arguments should exit 2, got ${status}"
fi

status=0
bash "$script" "${work}/missing" >/dev/null 2>&1 || status=$?
if [ "$status" -ne 2 ]; then
  fail "a missing directory should exit 2, got ${status}"
fi

mkdir -p "${work}/batch"
for i in $(seq 1 101); do
  printf '%s' "$formatted" > "${work}/batch/f${i}.go"
done
printf '%s' "$dirty" > "${work}/batch/zzz.go"
status=0
out=$(bash "$script" "${work}/batch" 2>&1) || status=$?
if [ "$status" -ne 1 ] || [[ "$out" != *"zzz.go"* ]]; then
  fail "a batch over 100 files should still name the unformatted file, status=${status} out=${out}"
fi
gofmt -w "${work}/batch/zzz.go"
if ! bash "$script" "${work}/batch"; then
  fail "a batch over 100 formatted files should pass"
fi

mkdir -p "${work}/many/a" "${work}/many/b"
printf '%s' "$formatted" > "${work}/many/a/a.go"
printf '%s' "$dirty" > "${work}/many/b/b.go"
status=0
out=$(bash "$script" "${work}/many/a" "${work}/many/b" 2>&1) || status=$?
if [ "$status" -ne 1 ] || [[ "$out" != *"b/b.go"* ]] || [[ "$out" == *"a/a.go"* ]]; then
  fail "only the unformatted directory should be reported, status=${status} out=${out}"
fi

if [ "$failures" -gt 0 ]; then
  echo "${failures} test(s) failed" >&2
  exit 1
fi
echo "ok - check-gofmt.sh"
