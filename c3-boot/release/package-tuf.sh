#!/usr/bin/env bash
# Packages the TUF part of a release slot from Sigstore's TUF metadata in
# testdata/tuf: each root newer than release/pinned-root.json, then
# targets.json and trusted_root.json. Then checks the part from the pinned
# root with the device's code, so a release never signs an image whose
# metadata a device would reject.
#
# Usage: release/package-tuf.sh OUT

set -euo pipefail

if (($# != 1)); then
  echo "usage: $0 OUT" >&2
  exit 2
fi
out="$1"
root="$(cd "$(dirname "$0")/.." && pwd)"
tuf="${root}/testdata/tuf"
pinned="${root}/release/pinned-root.json"

# Canonical JSON leaves a PEM key's newlines raw, which strict parsing
# rejects.
pinned_version="$(python3 -c '
import json, sys
print(json.loads(open(sys.argv[1]).read(), strict=False)["signed"]["version"])
' "${pinned}")"
roots=()
while read -r n; do
  roots+=("${tuf}/${n}.root.json")
done < <(
  for f in "${tuf}"/*.root.json; do
    n="$(basename "${f}" .root.json)"
    ((n > pinned_version)) && echo "${n}"
  done | sort -n
)

(cd "${root}" && cargo build -q --locked -p c3-ota)
ota() {
  "${root}/target/debug/c3-ota" "$@"
}
args=(--targets "${tuf}/targets.json" --trusted-root "${tuf}/trusted_root.json" --out "${out}")
if ((${#roots[@]} > 0)); then
  args+=(--roots "$(
    IFS=,
    echo "${roots[*]}"
  )")
fi
ota tuf-package "${args[@]}"
ota tuf-verify --pinned "${pinned}" --tuf "${out}"
