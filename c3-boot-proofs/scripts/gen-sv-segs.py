#!/usr/bin/env python3
"""Writes the segment theorems of `sigstore::verify` that `svseg.Segment`
composes from runs of generated stages, one file per segment.

Usage: python3 scripts/gen-sv-segs.py [name ...]   (from c3-boot-proofs/)
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svseg import Segment  # noqa: E402

SEGMENTS = {
    'SvSegLeaf': ('sv_seg_leaf', [('SvL1', 'sv_l1'), ('SvL2', 'sv_l2'), ('SvL3', 'sv_l3'), ('SvL4', 'sv_l4'),
                                  ('SvL5', 'sv_l5'), ('SvL6', 'sv_l6')],
                  "**The leaf certificate up to its extensions**: from 0x72 to the extensions loop at 0x4EA, "
                  "`sv_l1` to `sv_l6`."),
}


def opens(seq):
    """The namespaces the stages' files open, in order of first use."""
    out = []
    for fn, _ in seq:
        for line in open(f'C3BootProofs/Proofs/{fn}.lean'):
            if line.startswith('open '):
                out += [x for x in line.split()[1:] if x not in out]
    return out


def write(fname):
    name, seq, doc = SEGMENTS[fname]
    seg = Segment(name, seq, doc).build()
    out = ["import C3BootProofs.Proofs.SvSeg"]
    out += [f"import C3BootProofs.Proofs.{fn}" for fn, _ in seq]
    out += ["", "/-!", f"# `sigstore::verify`: {doc.split('**')[1].rstrip('.:')}", "",
            "Composed from generated stages by `scripts/gen-sv-segs.py`.", "-/", "",
            "namespace C3.RV32.Sv", "",
            "open " + " ".join(opens(seq)), "",
            "set_option maxRecDepth 100000", "", seg.lean(), "", "end C3.RV32.Sv", ""]
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    for f in sys.argv[1:] or SEGMENTS:
        write(f)
