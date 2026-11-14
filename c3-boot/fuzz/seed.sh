#!/usr/bin/env bash
# Writes seed inputs for each fuzz target into corpus/, built from the
# mutation test's fixtures: a valid slot, its bundle container, its empty
# chain and trust-root blob, its manifest and image header, and two
# boot-state records.

set -euo pipefail

fuzz="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "${fuzz}/.." && pwd)"
data="${root}/testdata"
work="$(mktemp -d)"
trap 'rm -rf "${work}"' EXIT
mkdir -p "${fuzz}"/corpus/{formats,trust,sigstore,slot}

(cd "${root}" && cargo build -q --locked -p c3-ota)
ota() {
  "${root}/target/debug/c3-ota" "$@"
}

ota container --bundle "${data}/mutation/bundle.sigstore.json" \
  --image "${data}/mutation/image.bin" --out "${work}/bundle"
ota chain --out "${work}/chain"
ota blob --trusted-root "${data}/mutation/trusted_root.json" --level 0 \
  --issuer https://token.actions.githubusercontent.com \
  --build-signer-uri https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main \
  --repository-id 1234 --owner-id 5678 --trigger push \
  --signers "0=${data}/keys/genesis-dev-1.seed,1=${data}/keys/genesis-dev-2.seed" \
  --out "${work}/blob"
ota slot --image "${data}/mutation/image.bin" --bundle "${work}/bundle" \
  --chain "${work}/chain" --blob "${work}/blob" --out "${fuzz}/corpus/slot/valid"
cp "${work}/bundle" "${fuzz}/corpus/sigstore/valid"
ota record --preferred b --trial a --boots 2 --confirmed b --generation 7 --out "${work}/record-a"
ota record --preferred a --confirmed a --generation 8 --out "${work}/record-b"

python3 - "${work}" "${data}/mutation/image.bin" "${fuzz}/corpus" <<'PY'
import struct
import sys

work, image_path, corpus = sys.argv[1:]
read = lambda name: open(f"{work}/{name}", "rb").read()
image = open(image_path, "rb").read()
slot = open(f"{corpus}/slot/valid", "rb").read()
chain = read("chain")
with open(f"{corpus}/trust/valid", "wb") as f:
    f.write(struct.pack("<H", len(chain)) + chain + read("blob"))
with open(f"{corpus}/formats/manifest", "wb") as f:
    f.write(b"\x00" + slot[:40])
with open(f"{corpus}/formats/image", "wb") as f:
    f.write(b"\x01" + struct.pack("<I", len(image)) + image)
with open(f"{corpus}/formats/records", "wb") as f:
    f.write(b"\x02" + read("record-a") + read("record-b"))
PY
echo "seeds written to ${fuzz}/corpus"
