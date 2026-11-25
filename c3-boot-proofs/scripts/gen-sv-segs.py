#!/usr/bin/env python3
"""Writes the segment theorems of `sigstore::verify` that `svseg.Segment`
composes from runs of generated stages, one file per segment.

Usage: python3 scripts/gen-sv-segs.py [--keep-going] [name ...]   (from c3-boot-proofs/)

With --keep-going, a file that can't be written yet is skipped.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svmerge import merged  # noqa: E402
from svseg import Segment  # noqa: E402

# Merged stages: (file, theorem, the stages, doc).
MERGES = [(f'SvWin{i}', f'sv_win{i}', (f'SvWin{i}e', f'sv_win{i}e'), (f'SvWin{i}n', f'sv_win{i}n'),
           f"validity-window check {i}, whichever way its high words compare") for i in range(8)] + [
    ('SvTr5', 'sv_tr5', ('SvTr5n', 'sv_tr5n'), ('SvTr5s', 'sv_tr5s'),
     "the timestamp's optional `[0]` field, present or not"),
    ('SvCr1', 'sv_cr1', ('SvCr1e', 'sv_cr1e'), ('SvCr1n', 'sv_cr1n'),
     "the entry's index against the checkpoint's size, whichever way the high words compare"),
    ('SvCk2', 'sv_ck2', ('SvCk2a', 'sv_ck2a'), ('SvCk2b', 'sv_ck2b'),
     "the checkpoint's size line, one digit or more"),
    ('SvTrv', 'sv_trv', ('SvTrvct', 'sv_trvct'), ('SvTrvmd', 'sv_trvmd'), ('SvTrvother', 'sv_trvother'),
     "one signed attribute's value: the content type, the message digest, or another"),
    ('SvTt3', 'sv_tt3', ('SvTt3n', 'sv_tt3n'), ('SvTt3s', 'sv_tt3s'), "the `TSTInfo`'s optional accuracy"),
    ('SvTt4n', 'sv_tt4n', ('SvTt4nn', 'sv_tt4nn'), ('SvTt4ns', 'sv_tt4ns'), "the byte after the `ordering` tag"),
    ('SvTt4b', 'sv_tt4b', ('SvTt4e1', 'sv_tt4e1'), ('SvSegTt4x1', 'sv_seg_tt4x1'),
     "after the `ordering` boolean, the end of the `TSTInfo` or more"),
    ('SvTt4', 'sv_tt4', ('SvTt4e0', 'sv_tt4e0'), ('SvSegTt4o', 'sv_seg_tt4o'), ('SvSegTt4x0', 'sv_seg_tt4x0'),
     "the `TSTInfo`'s optional `ordering` and `nonce`"),
    ('SvTt5', 'sv_tt5', ('SvTt5n', 'sv_tt5n'), ('SvTt5s', 'sv_tt5s'), "the `TSTInfo`'s optional `tsa` name"),
    ('SvTt6', 'sv_tt6', ('SvTt6n', 'sv_tt6n'), ('SvTt6s', 'sv_tt6s'), "the `TSTInfo`'s optional extensions"),
    ('SvCg', 'sv_cg', ('SvCg0', 'sv_cg0'), ('SvCg1', 'sv_cg1'), ('SvCg2', 'sv_cg2'), ('SvCg3', 'sv_cg3'),
     ('SvCg4', 'sv_cg4'), "one base64 group of a cosignature, padded at any of its places or not at all"),
    ('SvCm', 'sv_cm', ('SvCme', 'sv_cme'), ('SvCmdl', 'sv_cmdl'), ('SvCmdn', 'sv_cmdn'), ('SvCmf', 'sv_cmf'), ('SvCmk', 'sv_cmk'),
     ('SvCmn', 'sv_cmn'), ('SvCms', 'sv_cms'), ('SvCmx', 'sv_cmx'), "the end of a signature line, empty or not"),
    ('SvX2', 'sv_x2', ('SvX2z', 'sv_x2z'), ('SvX2n', 'sv_x2n'), ('SvSegX2c', 'sv_seg_x2c'),
     "an extension's criticality and value"),
    ('SvDbc2m', 'sv_dbc2m', ('SvDbc2e', 'sv_dbc2e'), ('SvDbc2', 'sv_dbc2'),
     "a `BasicConstraints` sequence, empty or not"),
    ('SvD', 'sv_d', ('SvSegDku', 'sv_seg_dku'), ('SvSegEku', 'sv_seg_eku'), ('SvSegDbc', 'sv_seg_dbc'),
     *[(f'SvDp{i}', f'sv_dp{i}') for i in range(6)],
     "an extension by its OID: `KeyUsage`, `ExtKeyUsage`, `BasicConstraints`, a policy OID, or another")]

SEGMENTS = {
    'SvSegDbc': ('sv_seg_dbc', [('SvDbc1', 'sv_dbc1'), ('SvDbc2m', 'sv_dbc2m')],
                 "**A `BasicConstraints` extension**: from the OID tests at 0x4E2 back to the extensions loop at "
                 "0x3B8, `sv_dbc1` and `sv_dbc2m`."),
    'SvSegCert': ('sv_seg_cert', [('SvSegLeaf', 'sv_seg_leaf'), ('SvExtLoop', 'sv_extloop_st'), ('SvL8a', 'sv_l8a'),
                                  ('SvISearch', 'sv_isearch_st'), ('SvLh', 'sv_lh'), ('SvDpv', 'sv_dpv')],
                  "**The leaf certificate and its issuer**: from 0x5C to the P-256 check at 0xA4C: the leaf, its "
                  "extensions, the intermediate that issued it, the leaf's signature, and the policy."),
    'SvSegTs': ('sv_seg_ts', [('SvSegTr', 'sv_seg_tr'), ('SvSegAttrPre', 'sv_seg_attr_pre'),
                              ('SvAttrLoop', 'sv_attrloop_st'), ('SvSegTt', 'sv_seg_tt'),
                              ('SvTSearch', 'sv_tsearch_st'), ('SvTsig', 'sv_tsig'), ('SvTp', 'sv_tp')],
                "**The timestamp**: from 0xA60 to the checkpoint at 0x142E: the timestamp response, its signed "
                "attributes, the `TSTInfo`, the TSA that signed it, and its signature."),
    'SvSegLog': ('sv_seg_log', [('SvSegCkpt', 'sv_seg_ck'), ('SvCkdLoop', 'sv_ckdloop_run'),
                                ('SvCSearch', 'sv_csearch_st'), ('SvCs1', 'sv_cs1'),
                                ('SvCosigLoop', 'sv_cosigloop_st0'), ('SvSegWin', 'sv_seg_win')],
                 "**The transparency log entry**: from the checkpoint at 0x142E to the successful exit at 0x1A9E: "
                 "the checkpoint, the log that signed it, its signatures, the entry's index, and the validity "
                 "windows."),
    'SvSegSv': ('sv_seg_sv', [('SvSegCert', 'sv_seg_cert'), ('SvP2St', 'sv_p2st'), ('SvSegTs', 'sv_seg_ts'),
                              ('SvSegLog', 'sv_seg_log')],
                "**`sigstore::verify` to its successful exit**: from 0x5C to 0x1A9E: the leaf certificate and its "
                "issuer, the P-256 check of the artifact's signature, the timestamp, and the transparency log "
                "entry."),
    'SvSegEku': ('sv_seg_eku', [('SvDeku1', 'sv_deku1'), ('SvEkuLoop', 'sv_ekuloop_st')],
                 "**An `ExtKeyUsage` extension**: from the OID tests at 0x4E2 back to the extensions loop at "
                 "0x3B8, `sv_deku1` and the loop over its OIDs."),
    'SvSegExt': ('sv_seg_ext', [('SvX1', 'sv_x1'), ('SvX2', 'sv_x2'), ('SvD', 'sv_d')],
                 "**One extension of the leaf**: from the extensions loop's head at 0x3B8 back to it, `sv_x1`, "
                 "`sv_x2`, and `sv_d`."),
    'SvSegDku': ('sv_seg_dku', [('SvDku1', 'sv_dku1'), ('SvDku2', 'sv_dku2')],
                 "**A `KeyUsage` extension**: from the OID tests at 0x4E2 back to the extensions loop at 0x3B8, "
                 "`sv_dku1` and `sv_dku2`."),
    'SvSegX2c': ('sv_seg_x2c', [('SvX2c', 'sv_x2c'), ('SvX2t', 'sv_x2t')],
                 "**A critical extension's value**: from 0x42C to the OID tests at 0x4E2, `sv_x2c` and `sv_x2t`."),
    'SvSegLeaf': ('sv_seg_leaf', [('SvL1', 'sv_l1'), ('SvL2', 'sv_l2'), ('SvL3', 'sv_l3'), ('SvL4', 'sv_l4'),
                                  ('SvL5', 'sv_l5'), ('SvL6', 'sv_l6')],
                  "**The leaf certificate up to its extensions**: from 0x5C to the extensions loop at 0x3B8, "
                  "`sv_l1` to `sv_l6`."),
    'SvSegTr': ('sv_seg_tr', [('SvTr1', 'sv_tr1'), ('SvTr2', 'sv_tr2'), ('SvTr3', 'sv_tr3'), ('SvTr4', 'sv_tr4'),
                              ('SvTr5', 'sv_tr5'), ('SvTr6', 'sv_tr6'), ('SvTr7', 'sv_tr7')],
                "**The timestamp up to its signed attributes**: from 0xA60 to the attributes loop at 0xEA0, "
                "`sv_tr1` to `sv_tr7`."),
    'SvSegCkpt': ('sv_seg_ck', [('SvCk1', 'sv_ck1'), ('SvCk2', 'sv_ck2')],
                  "**The checkpoint's origin and size**: from 0x142E to the size loop at 0x14FE, `sv_ck1` and "
                  "`sv_ck2`."),
    'SvSegTt4x1': ('sv_seg_tt4x1', [('SvTt4x1', 'sv_tt4x1'), ('SvTt4n', 'sv_tt4n')],
                   "**The nonce after the `ordering` boolean**: from 0x124A to 0x1272."),
    'SvSegTt4x0': ('sv_seg_tt4x0', [('SvTt4x0', 'sv_tt4x0'), ('SvTt4n', 'sv_tt4n')],
                   "**The nonce with no `ordering`**: from 0x121E to 0x1272."),
    'SvSegTt4o': ('sv_seg_tt4o', [('SvTt4o', 'sv_tt4o'), ('SvTt4b', 'sv_tt4b')],
                  "**The `ordering` boolean and what follows it**: from 0x121E to 0x1272."),
    'SvSegTt': ('sv_seg_tt', [('SvTt1', 'sv_tt1'), ('SvTt2', 'sv_tt2'), ('SvTt3', 'sv_tt3'), ('SvTt4', 'sv_tt4'),
                              ('SvTt5', 'sv_tt5'), ('SvTt6', 'sv_tt6'), ('SvTsv', 'sv_tsv')],
                "**The `TSTInfo` and the timestamp's signature**: from 0x10A4 to the TSA search at 0x1344, "
                "`sv_tt1` to `sv_tsv`."),
    'SvSegAttrPre': ('sv_seg_attr_pre', [('SvTra', 'sv_tra'), ('SvTrv', 'sv_trv')],
                     "**The first signed attribute**: from 0xEA0 to the attributes loop's branch at 0xFF8."),
    'SvSegAttr': ('sv_seg_attr', [('SvTrl', 'sv_trl'), ('SvTra', 'sv_tra'), ('SvTrv', 'sv_trv')],
                  "**One more signed attribute**: from the attributes loop's branch at 0xFF8 back to it."),
    'SvSegCosig': ('sv_seg_cosig', [('SvCsa', 'sv_csa'), ('SvNSearch', 'sv_nsearch_run'), ('SvCgLoop', 'sv_cgloop_run')],
                   "**One signature line of the checkpoint**: from the signature loop's head at 0x1642 back to it."),
    'SvSegWin': ('sv_seg_win', [('SvCr1', 'sv_cr1'), ('SvRl', 'sv_rl'), ('SvRm', 'sv_rm')] +
                 [(f'SvWin{i}', f'sv_win{i}') for i in range(8)],
                 "**The entry's index and the validity windows**: from 0x17F8 to the successful exit at 0x1A9E, "
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
ORDER = ['SvTt4n', 'SvSegTt4x1', 'SvSegTt4x0', 'SvTt4b', 'SvSegTt4o', 'SvTt4',
         'SvDbc2m', 'SvSegDbc', 'SvSegDku', 'SvSegEku', 'SvSegX2c', 'SvX2', 'SvD', 'SvSegExt']


def build(f):
    for fn, nm, *vs, doc in MERGES:
        if fn == f:
            merged(fn, nm, vs, doc[0].upper() + doc[1:] + ".")
            return
    write(f)


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a != '--keep-going']
    keep_going = len(args) < len(sys.argv) - 1
    names = args or (ORDER + [fn for fn, *_ in MERGES if fn not in ORDER] + [f for f in SEGMENTS if f not in ORDER])
    for f in names:
        try:
            build(f)
        except ValueError as e:
            # A file may need one that a later script writes.
            if not keep_going:
                raise
            print(f"{f}: not yet ({e})", file=sys.stderr)
