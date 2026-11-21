#!/usr/bin/env python3
"""Writes the segment theorems of `sigstore::verify` that `svseg.Segment`
composes from runs of generated stages, one file per segment.

Usage: python3 scripts/gen-sv-segs.py [name ...]   (from c3-boot-proofs/)
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svmerge import merged  # noqa: E402
from svseg import Segment  # noqa: E402

# Merged stages: (file, theorem, the two stages, doc).
MERGES = [(f'SvWin{i}', f'sv_win{i}', (f'SvWin{i}e', f'sv_win{i}e'), (f'SvWin{i}n', f'sv_win{i}n'),
           f"validity-window check {i}, whichever way its high words compare") for i in range(8)] + [
    ('SvTsa4', 'sv_tsa4', ('SvTsa4n', 'sv_tsa4n'), ('SvTsa4s', 'sv_tsa4s'),
     "the timestamp's optional `[0]` field, present or not"),
    ('SvCr1', 'sv_cr1', ('SvCr1e', 'sv_cr1e'), ('SvCr1n', 'sv_cr1n'),
     "the entry's index against the checkpoint's size, whichever way the high words compare"),
    ('SvCk2', 'sv_ck2', ('SvCk2a', 'sv_ck2a'), ('SvCk2b', 'sv_ck2b'),
     "the checkpoint's size line, one digit or more")]

SEGMENTS = {
    'SvSegLeaf': ('sv_seg_leaf', [('SvL1', 'sv_l1'), ('SvL2', 'sv_l2'), ('SvL3', 'sv_l3'), ('SvL4', 'sv_l4'),
                                  ('SvL5', 'sv_l5'), ('SvL6', 'sv_l6')],
                  "**The leaf certificate up to its extensions**: from 0x72 to the extensions loop at 0x4EA, "
                  "`sv_l1` to `sv_l6`."),
    'SvSegTsa': ('sv_seg_tsa', [('SvTsa1', 'sv_tsa1'), ('SvTsa2', 'sv_tsa2'), ('SvTsa3', 'sv_tsa3'),
                                ('SvTsa4', 'sv_tsa4'), ('SvTsa5', 'sv_tsa5')],
                 "**The timestamp up to its signed attributes**: from 0x2034 to the attributes loop at 0x2506, "
                 "`sv_tsa1` to `sv_tsa5`."),
    'SvSegDpv': ('sv_seg_dpv', [('SvDpv', 'sv_dpv'), ('SvTs1', 'sv_ts1')],
                 "**The policy, then the signature's DER**: from 0xDE6 to the P-256 check at 0xFBA, `sv_dpv` and "
                 "`sv_ts1`."),
    'SvSegCkpt': ('sv_seg_ck', [('SvCk1', 'sv_ck1'), ('SvCk2', 'sv_ck2')],
                "**The checkpoint's origin and size**: from 0x2B34 to the size loop at 0x2C06, `sv_ck1` and "
                "`sv_ck2`."),
    'SvSegWin': ('sv_seg_win', [('SvCr1', 'sv_cr1'), ('SvRl', 'sv_rl'), ('SvRm', 'sv_rm')] +
                 [(f'SvWin{i}', f'sv_win{i}') for i in range(8)],
                 "**The entry's index and the validity windows**: from 0x2F5A to the successful exit at 0x3264, "
                 "`sv_cr1`, `sv_rl`, `sv_rm`, and the eight window checks."),
}


def opens(seq):
    """The namespaces the stages' files open, in order of first use."""
    out = []
    for fn, _ in [y for x in seq for y in (x[1] if x[0] == 'merge' else [x])]:
        for line in open(f'C3BootProofs/Proofs/{fn}.lean'):
            if line.startswith('open '):
                out += [x for x in line.split()[1:] if x not in out]
    return out


def write(fname):
    name, seq, doc = SEGMENTS[fname]
    seg = Segment(name, seq, doc).build()
    out = ["import C3BootProofs.Proofs.SvSegCk" if fname == 'SvSegCkpt' else "import C3BootProofs.Proofs.SvSeg"]
    for x in seq:
        out += [f"import C3BootProofs.Proofs.{fn}" for fn, _ in (x[1] if x[0] == 'merge' else [x])]
    out += ["", "/-!", f"# `sigstore::verify`: {doc.split('**')[1].rstrip('.:')}", "",
            "Composed from generated stages by `scripts/gen-sv-segs.py`.", "-/", "",
            "namespace C3.RV32.Sv", "",
            "open " + " ".join(opens(seq)), "",
            "set_option maxRecDepth 100000", "", seg.lean(), "", "end C3.RV32.Sv", ""]
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    for fn, nm, va, vb, doc in MERGES:
        merged(fn, nm, va, vb, doc[0].upper() + doc[1:] + ".")
    for f in sys.argv[1:] or SEGMENTS:
        write(f)
