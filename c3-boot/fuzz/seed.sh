#!/usr/bin/env bash
# Writes seed inputs for each fuzz target into corpus/, built from the
# mutation test's fixtures: a valid slot with a development TUF part, its
# bundle container, its manifest and image header, and two boot-state
# records. The TUF target's seeds are Sigstore's TUF metadata from
# testdata/tuf/ and its trusted_root.json.

set -euo pipefail

fuzz="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "${fuzz}/.." && pwd)"
data="${root}/testdata"
work="$(mktemp -d)"
trap 'rm -rf "${work}"' EXIT
mkdir -p "${fuzz}"/corpus/{formats,sigstore,slot,tuf}

(cd "${root}" && cargo build -q --locked -p c3-ota)
ota() {
  "${root}/target/debug/c3-ota" "$@"
}

ota container --bundle "${data}/mutation/bundle.sigstore.json" \
  --image "${data}/mutation/image.bin" --out "${work}/bundle"
ota tuf-dev-targets --keys "${data}/keys" --root-version 1 \
  --trusted-root "${data}/mutation/trusted_root.json" --out "${work}/targets"
ota tuf-package --targets "${work}/targets" \
  --trusted-root "${data}/mutation/trusted_root.json" --out "${work}/dev-tuf"
ota slot --image "${data}/mutation/image.bin" --bundle "${work}/bundle" \
  --tuf "${work}/dev-tuf" --out "${fuzz}/corpus/slot/valid"
cp "${work}/bundle" "${fuzz}/corpus/sigstore/valid"
roots=()
for v in $(seq 6 16); do
  roots+=("${data}/tuf/${v}.root.json")
done
ota tuf-package --roots "$(IFS=,; echo "${roots[*]}")" --targets "${data}/tuf/targets.json" \
  --trusted-root "${data}/tuf/trusted_root.json" --out "${work}/tuf"
{ printf '\x01'; cat "${work}/tuf"; } > "${fuzz}/corpus/tuf/sigstore"
{ printf '\x00'; cat "${data}/tuf/trusted_root.json"; } > "${fuzz}/corpus/tuf/trusted-root"
{ printf '\x00'; cat "${data}/tuf/16.root.json"; } > "${fuzz}/corpus/tuf/root"
ota record --preferred b --trial a --boots 2 --confirmed b --generation 7 --out "${work}/record-a"
ota record --preferred a --confirmed a --generation 8 --out "${work}/record-b"

python3 - "${work}" "${data}/mutation/image.bin" "${fuzz}/corpus" <<'PY'
import struct
import sys

work, image_path, corpus = sys.argv[1:]
read = lambda name: open(f"{work}/{name}", "rb").read()
image = open(image_path, "rb").read()
slot = open(f"{corpus}/slot/valid", "rb").read()
with open(f"{corpus}/formats/manifest", "wb") as f:
    f.write(b"\x00" + slot[:32])
with open(f"{corpus}/formats/image", "wb") as f:
    f.write(b"\x01" + struct.pack("<I", len(image)) + image)
with open(f"{corpus}/formats/records", "wb") as f:
    f.write(b"\x02" + read("record-a") + read("record-b"))
PY
echo "seeds written to ${fuzz}/corpus"
