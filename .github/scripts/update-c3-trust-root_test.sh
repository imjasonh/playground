#!/usr/bin/env bash
# Tests update-c3-trust-root.sh fetch against local copies of
# sigstore/root-signing's files, in a scratch git repository.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
repo_root="$(cd "${here}/../.." && pwd)"
script="${here}/update-c3-trust-root.sh"
work="$(mktemp -d)"
trap 'rm -rf "${work}"' EXIT

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

# setup makes a scratch repository holding c3-boot/release and
# c3-boot/testdata/tuf, and a copy of sigstore/root-signing whose files match
# them, with a Rekor v1 log added to the signing configuration as Sigstore
# publishes it.
setup() {
  rm -rf "${work}/repo" "${work}/src"
  mkdir -p "${work}/repo/c3-boot/testdata" "${work}/src/targets" "${work}/src/metadata/root_history"
  cp -r "${repo_root}/c3-boot/release" "${work}/repo/c3-boot/release"
  cp -r "${repo_root}/c3-boot/testdata/tuf" "${work}/repo/c3-boot/testdata/tuf"
  git -C "${work}/repo" init -q -b main
  git -C "${work}/repo" -c user.name=t -c user.email=t@example.com add -A
  git -C "${work}/repo" -c user.name=t -c user.email=t@example.com commit -q -m init
  local tuf="${repo_root}/c3-boot/testdata/tuf" newest
  cp "${tuf}"/*.root.json "${work}/src/metadata/root_history/"
  newest=$(find "${tuf}" -name '*.root.json' -printf '%f\n' | sort -n | tail -1)
  cp "${tuf}/${newest}" "${work}/src/metadata/root.json"
  cp "${tuf}/targets.json" "${work}/src/metadata/targets.json"
  cp "${repo_root}/c3-boot/release/trusted_root.json" "${work}/src/targets/trusted_root.json"
  python3 - "${repo_root}/c3-boot/release/signing_config.json" \
    "${work}/src/targets/signing_config_rekor_v2.v0.2.json" <<'EOF'
import json
import sys

config = json.load(open(sys.argv[1]))
config["rekorTlogUrls"].append({
    "url": "https://rekor.sigstore.dev",
    "majorApiVersion": 1,
    "validFor": {"start": "2021-01-12T11:53:27.000Z"},
    "operator": "sigstore.dev",
})
json.dump(config, open(sys.argv[2], "w"), indent=2)
EOF
}

# fetch runs the script's fetch step in the scratch repository.
fetch() {
  (
    cd "${work}/repo"
    GITHUB_OUTPUT="${work}/output" C3_ROOT_SIGNING_DIR="${work}/src" \
      C3_ROOT_SIGNING_COMMIT="$1" bash "${script}" fetch
  )
}

commit="0123456789abcdef0123456789abcdef01234567"

# The same files, except for the Rekor v1 log, change nothing.
setup
: >"${work}/output"
fetch "${commit}"
grep -qx "result=unchanged" "${work}/output" || fail "unchanged: $(cat "${work}/output")"
[[ "$(git -C "${work}/repo" rev-parse --abbrev-ref HEAD)" == main ]] || fail "unchanged: left main"

# A changed trusted root updates the files and the README on a new branch.
setup
python3 - "${work}/src/targets/trusted_root.json" <<'EOF'
import json
import sys

root = json.load(open(sys.argv[1]))
root["tlogs"][-1]["publicKey"]["validFor"]["start"] = "2025-09-24T00:00:00Z"
json.dump(root, open(sys.argv[1], "w"), indent=2)
EOF
: >"${work}/output"
fetch "${commit}"
grep -qx "result=changed" "${work}/output" || fail "changed: $(cat "${work}/output")"
grep -qx "commit=${commit}" "${work}/output" || fail "changed: no commit output"
release="${work}/repo/c3-boot/release"
cmp -s "${work}/src/targets/trusted_root.json" "${release}/trusted_root.json" || fail "changed: trusted root not copied"
cmp -s "${work}/src/targets/trusted_root.json" "${work}/repo/c3-boot/testdata/tuf/trusted_root.json" ||
  fail "changed: TUF trusted root not copied"
grep -qx "${commit}" "${work}/repo/c3-boot/testdata/tuf/COMMIT" || fail "changed: TUF COMMIT not updated"
python3 - "${release}/signing_config.json" <<'EOF' || fail "changed: signing configuration still lists a non-v2 log"
import json
import sys

logs = json.load(open(sys.argv[1]))["rekorTlogUrls"]
assert [l["majorApiVersion"] for l in logs] == [2], logs
EOF
grep -q "commit \`${commit}\`" "${release}/README.md" || fail "changed: README commit not updated"
sum=$(sha256sum "${release}/trusted_root.json" | cut -d' ' -f1)
grep -q "\`${sum}\`" "${release}/README.md" || fail "changed: README SHA-256 not updated"
[[ "$(git -C "${work}/repo" rev-parse --abbrev-ref HEAD)" == automation/c3-trust-root ]] ||
  fail "changed: not on the automation branch"
[[ -z "$(git -C "${work}/repo" status --porcelain)" ]] || fail "changed: uncommitted files"

# A new root version adds its file and leaves the trusted root alone.
setup
python3 - "${work}/src/metadata/root.json" "${work}/src/metadata/root_history" <<'EOF'
import json
import sys

root = json.load(open(sys.argv[1]))
root["signed"]["version"] += 1
for path in (sys.argv[1], f"{sys.argv[2]}/{root['signed']['version']}.root.json"):
    json.dump(root, open(path, "w"), indent=2)
EOF
newest=$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["signed"]["version"])' \
  "${work}/src/metadata/root.json")
: >"${work}/output"
fetch "${commit}"
grep -qx "result=changed" "${work}/output" || fail "new root: $(cat "${work}/output")"
tufdir="${work}/repo/c3-boot/testdata/tuf"
cmp -s "${work}/src/metadata/root.json" "${tufdir}/${newest}.root.json" || fail "new root: not copied"
[[ -e "${tufdir}/5.root.json" ]] || fail "new root: dropped the oldest root"
git -C "${work}/repo" diff --quiet HEAD~1 -- c3-boot/release/trusted_root.json ||
  fail "new root: changed the trusted root"
[[ -z "$(git -C "${work}/repo" status --porcelain)" ]] || fail "new root: uncommitted files"

# A signing configuration with no Rekor v2 log fails.
setup
python3 - "${work}/src/targets/signing_config_rekor_v2.v0.2.json" <<'EOF'
import json
import sys

config = json.load(open(sys.argv[1]))
config["rekorTlogUrls"] = [l for l in config["rekorTlogUrls"] if l["majorApiVersion"] != 2]
json.dump(config, open(sys.argv[1], "w"), indent=2)
EOF
if fetch "${commit}" 2>/dev/null; then
  fail "no Rekor v2 log: fetch succeeded"
fi

echo "PASS"
