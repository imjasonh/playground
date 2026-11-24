#!/usr/bin/env bash
# Copies Sigstore's production TUF metadata from sigstore/root-signing at
# one commit into this directory: root versions FIRST through the newest,
# targets.json, and the trusted_root.json target that targets.json lists.
#
# Usage: testdata/tuf/fetch.sh COMMIT [FIRST]
#
# FIRST defaults to 5, the first root whose keys are PEM-encoded, which is
# the only form c3-verify reads.
set -euo pipefail

commit="${1:?usage: fetch.sh COMMIT [FIRST]}"
first="${2:-5}"
dir="$(cd "$(dirname "$0")" && pwd)"
base="https://raw.githubusercontent.com/sigstore/root-signing/${commit}"

_get() {
  curl -fsSL --retry 4 -o "$2" "${base}/$1"
}

_get metadata/root.json "${dir}/root.json.tmp"
newest="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["signed"]["version"])' \
  "${dir}/root.json.tmp")"
rm "${dir}/root.json.tmp"
rm -f "${dir}"/*.root.json
for ((v = first; v <= newest; v++)); do
  _get "metadata/root_history/${v}.root.json" "${dir}/${v}.root.json"
done
_get metadata/targets.json "${dir}/targets.json"
_get targets/trusted_root.json "${dir}/trusted_root.json"
echo "${commit}" >"${dir}/COMMIT"
echo "fetched roots ${first} through ${newest} at ${commit}"
