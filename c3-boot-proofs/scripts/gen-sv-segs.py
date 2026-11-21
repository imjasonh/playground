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
     "the checkpoint's size line, one digit or more"),
    ('SvTsav', 'sv_tsav', ('SvTsavct', 'sv_tsavct'), ('SvTsavmd', 'sv_tsavmd'), ('SvTsavother', 'sv_tsavother'),
     "one signed attribute's value: the content type, the message digest, or another"),
    ('SvTst3', 'sv_tst3', ('SvTst3n', 'sv_tst3n'), ('SvTst3s', 'sv_tst3s'), "the `TSTInfo`'s optional accuracy"),
    ('SvTst4n', 'sv_tst4n', ('SvTst4nn', 'sv_tst4nn'), ('SvTst4ns', 'sv_tst4ns'), "the byte after the `ordering` tag"),
    ('SvTst4b', 'sv_tst4b', ('SvTst4e1', 'sv_tst4e1'), ('SvSegTst4x1', 'sv_seg_tst4x1'),
     "after the `ordering` boolean, the end of the `TSTInfo` or more"),
    ('SvTst4', 'sv_tst4', ('SvTst4e0', 'sv_tst4e0'), ('SvSegTst4o', 'sv_seg_tst4o'), ('SvSegTst4x0', 'sv_seg_tst4x0'),
     "the `TSTInfo`'s optional `ordering` and `nonce`"),
    ('SvTst5', 'sv_tst5', ('SvTst5n', 'sv_tst5n'), ('SvTst5s', 'sv_tst5s'), "the `TSTInfo`'s optional `tsa` name"),
    ('SvTst6', 'sv_tst6', ('SvTst6n', 'sv_tst6n'), ('SvTst6s', 'sv_tst6s'), "the `TSTInfo`'s optional extensions"),
    ('SvCg', 'sv_cg', ('SvCg0', 'sv_cg0'), ('SvCg1', 'sv_cg1'), ('SvCg2', 'sv_cg2'), ('SvCg3', 'sv_cg3'),
     ('SvCg4', 'sv_cg4'), "one base64 group of a cosignature, padded at any of its places or not at all"),
    ('SvCm', 'sv_cm', ('SvCme', 'sv_cme'), ('SvCmdl', 'sv_cmdl'), ('SvCmdn', 'sv_cmdn'), ('SvCmf', 'sv_cmf'), ('SvCmk', 'sv_cmk'),
     ('SvCmn', 'sv_cmn'), ('SvCms', 'sv_cms'), ('SvCmx', 'sv_cmx'), "the end of a signature line, empty or not")]

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
    'SvSegTst4x1': ('sv_seg_tst4x1', [('SvTst4x1', 'sv_tst4x1'), ('SvTst4n', 'sv_tst4n')],
                    "**The nonce after the `ordering` boolean**: from 0x2918 to 0x2952."),
    'SvSegTst4x0': ('sv_seg_tst4x0', [('SvTst4x0', 'sv_tst4x0'), ('SvTst4n', 'sv_tst4n')],
                    "**The nonce with no `ordering`**: from 0x28DA to 0x2952."),
    'SvSegTst4o': ('sv_seg_tst4o', [('SvTst4o', 'sv_tst4o'), ('SvTst4b', 'sv_tst4b')],
                   "**The `ordering` boolean and what follows it**: from 0x28DA to 0x2952."),
    'SvSegTst': ('sv_seg_tst', [('SvTst1', 'sv_tst1'), ('SvTst2', 'sv_tst2'), ('SvTst3', 'sv_tst3'), ('SvTst4', 'sv_tst4'),
                                ('SvTst5', 'sv_tst5'), ('SvTst6', 'sv_tst6'), ('SvTsv', 'sv_tsv')],
                 "**The `TSTInfo` and the timestamp's signature**: from 0x2704 to the TSA search at 0x2A40, "
                 "`sv_tst1` to `sv_tsv`."),
    'SvSegAttrPre': ('sv_seg_attr_pre', [('SvTsaa', 'sv_tsaa'), ('SvTsav', 'sv_tsav')],
                     "**The first signed attribute**: from 0x2506 to the attributes loop's branch at 0x267A."),
    'SvSegAttr': ('sv_seg_attr', [('SvTsal', 'sv_tsal'), ('SvTsaa', 'sv_tsaa'), ('SvTsav', 'sv_tsav')],
                  "**One more signed attribute**: from the attributes loop's branch at 0x267A back to it."),
    'SvSegCosig': ('sv_seg_cosig', [('SvCsa', 'sv_csa'), ('SvNSearch', 'sv_nsearch_run'), ('SvCgLoop', 'sv_cgloop_run')],
                   "**One signature line of the checkpoint**: from the signature loop's head at 0x2D6E back to it."),
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
    out = ["import C3BootProofs.Proofs.SvSegCk"]
    for x in seq:
        out += [f"import C3BootProofs.Proofs.{fn}" for fn, _ in (x[1] if x[0] == 'merge' else [x])]
    out += ["", "/-!", f"# `sigstore::verify`: {doc.split('**')[1].rstrip('.:')}", "",
            "Composed from generated stages by `scripts/gen-sv-segs.py`.", "-/", "",
            "namespace C3.RV32.Sv", "",
            "open " + " ".join(opens(seq)), "",
            "set_option maxRecDepth 100000", "", seg.lean(), "", "end C3.RV32.Sv", ""]
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))


# Merges and segments that others are built from, in the order to write them.
ORDER = ['SvTst4n', 'SvSegTst4x1', 'SvSegTst4x0', 'SvTst4b', 'SvSegTst4o', 'SvTst4']


def build(f):
    for fn, nm, *vs, doc in MERGES:
        if fn == f:
            merged(fn, nm, vs, doc[0].upper() + doc[1:] + ".")
            return
    write(f)


if __name__ == "__main__":
    if sys.argv[1:]:
        for f in sys.argv[1:]:
            build(f)
    else:
        for f in ORDER:
            build(f)
        for fn, *_ in MERGES:
            if fn not in ORDER:
                build(fn)
        for f in SEGMENTS:
            if f not in ORDER:
                build(f)
