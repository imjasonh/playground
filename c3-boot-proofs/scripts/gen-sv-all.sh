#!/usr/bin/env bash
# Writes the composed theorems of `sigstore::verify` in an order that works.
# Each phase writes files that a later phase reads:
#
# 1. The merges and segments that no loop runs through (gen-sv-segs.py
#    writes them), then the searches and the loops over one stage.
# 2. `SvEkuLoop`, then the segments that end in it, one at a time, up to
#    `SvSegExt`, then `SvExtLoop`, whose body `SvSegExt` is.
# 3. Every segment, then the loops over `SvSegAttr` and `SvSegCosig`, then
#    every segment again, since `SvSegTs` and `SvSegLog` run through those
#    loops.
# 4. The theorems from 0x5C and from the entry to the return, and the latter
#    for a Bundle and a SigstoreRoot.
#
# The scripts ask Lean for some theorems' binders, so each phase builds the
# files it wrote before the next phase runs, and stops the script if they
# don't build. Run from c3-boot-proofs/ after the stages' .olean files are
# built.
set -euo pipefail
stamp=$(mktemp)
trap 'rm -f "$stamp"' EXIT

phase() {
  touch "$stamp"
  sleep 1
  echo "== $*"
  python3 "$@"
  local mods
  mods=$(find C3BootProofs/Proofs -name '*.lean' -newer "$stamp" | sed 's|/|.|g; s|\.lean$||')
  if [[ -n "$mods" ]]; then
    # shellcheck disable=SC2086
    lake build $mods
  fi
}

phase scripts/gen-sv-segs.py SvTt4n SvSegTt4x1 SvSegTt4x0 SvTt4b SvSegTt4o SvTt4 SvDbc2m SvSegDbc SvSegDku \
  SvWin0 SvWin1 SvWin2 SvWin3 SvWin4 SvWin5 SvWin6 SvWin7 SvTr5 SvCr1 SvCk2 SvTrv SvTt3 SvTt5 SvTt6 SvCg SvCm
phase scripts/gen-sv-search.py
phase scripts/gen-sv-loop.py
phase scripts/gen-sv-relloop.py SvEkuLoop
for f in SvSegEku SvSegX2c SvX2 SvD SvSegExt; do
  phase scripts/gen-sv-segs.py "$f"
done
phase scripts/gen-sv-relloop.py SvExtLoop
phase scripts/gen-sv-segs.py
phase scripts/gen-sv-attrloop.py
phase scripts/gen-sv-relloop.py SvCosigLoop
phase scripts/gen-sv-segs.py
phase scripts/gen-sv-top.py
phase scripts/gen-sv-entry.py
phase scripts/gen-sv-layout.py
