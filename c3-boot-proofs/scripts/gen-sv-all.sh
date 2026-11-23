#!/usr/bin/env bash
# Writes the composed theorems of `sigstore::verify` in an order that works:
# sv_p256 as a stage, merges (gen-sv-segs.py writes them, and loops use
# them), then searches and loops, then the segments, since segments use
# loops, then the loops over segments, then the segments that use those, and
# last the theorems from 0x72 and from the entry to the return, and the
# latter for a Bundle and a SigstoreRoot.
# The scripts ask Lean for some theorems' binders, so each phase builds the
# files it wrote before the next phase runs. A file whose imports a later
# phase rewrites may fail to build until then, so only the last build, of
# every file the phases wrote, has to pass. Run from c3-boot-proofs/ after
# the stages' .olean files are built.
set -euo pipefail
stamp=$(mktemp)
first=$(mktemp)
trap 'rm -f "$stamp" "$first"' EXIT

phase() {
  touch "$stamp"
  sleep 1
  python3 "$@"
  local mods
  mods=$(find C3BootProofs/Proofs -name '*.lean' -newer "$stamp" | sed 's|/|.|g; s|\.lean$||')
  if [[ -n "$mods" ]]; then
    # shellcheck disable=SC2086
    lake build $mods >/dev/null 2>&1 || echo "$1: some files don't build yet"
  fi
}

phase scripts/gen-sv-p256st.py
phase scripts/gen-sv-segs.py --keep-going
phase scripts/gen-sv-search.py
phase scripts/gen-sv-loop.py
phase scripts/gen-sv-attrloop.py
phase scripts/gen-sv-segs.py --keep-going
phase scripts/gen-sv-relloop.py
phase scripts/gen-sv-segs.py
phase scripts/gen-sv-top.py
phase scripts/gen-sv-entry.py
phase scripts/gen-sv-layout.py
# shellcheck disable=SC2046
lake build $(find C3BootProofs/Proofs -name '*.lean' -newer "$first" | sed 's|/|.|g; s|\.lean$||')
