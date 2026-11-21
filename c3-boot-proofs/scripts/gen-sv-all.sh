#!/usr/bin/env bash
# Writes the composed theorems of `sigstore::verify` in an order that works:
# merges first (gen-sv-segs.py writes them, and loops use them), then
# searches and loops, then the segments again, since segments use loops.
# Run from c3-boot-proofs/ after the stages' .olean files are built, because
# the scripts ask Lean for some stages' binders.
set -euo pipefail
python3 scripts/gen-sv-segs.py
python3 scripts/gen-sv-search.py
python3 scripts/gen-sv-loop.py
python3 scripts/gen-sv-attrloop.py
python3 scripts/gen-sv-segs.py
