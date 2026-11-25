#!/usr/bin/env python3
"""Writes `SvTop.lean`: `sigstore::verify` from 0x72 to its return.

`sv_seg_sv` runs from 0x72 to the successful exit at 0x3264, and
`sv_ok_3264` from there to the return of `Ok`. `sv_verify_72` joins them:
`sigstore::verify` returns `Err`, panics, or meets the success condition
and returns `Ok` with the timestamp's and the entry's index's words in
`out`.

Usage: python3 scripts/gen-sv-top.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import Stage, fname, groups, strip_parens, top_split  # noqa: E402
from svmerge import sc_pattern  # noqa: E402

SEG = ('SvSegSv', 'sv_seg_sv')
NEED = {'w3c': 'tlo', 'w78': 'thi', 'r25': 'ilo', 'r23': 'ihi'}


def main():
    st = Stage(*SEG)
    src = open(f'C3BootProofs/Proofs/{SEG[0]}.lean').read()
    i = src.index(f'theorem {SEG[1]} ')
    stmt = src[i:src.index(':= by\n', i)]
    header = stmt.split('\n', 1)[0][len(f'theorem {SEG[1]} '):]
    facts = {f.key: f for f in st.facts}
    vals = {k: strip_parens(top_split(facts[k].text, ' = ')[-1]) for k in NEED}
    nm = sc_pattern(st)
    pats = []
    for f in st.facts:
        if f.key == 'STEPS':
            pats += ["n1", "c1"]
        else:
            pats.append({'ST': 's1', 'E': 'E1', 'V': 'V1', 'FR': 'fR1'}.get(f.key, fname(f.key, 1)))
    pat = {f.key: p for f, p in zip([f for f in st.facts if f.key != 'STEPS'], pats[2:])}
    hyps = [g for g in groups(stmt[stmt.index('(FW : '):stmt.index('\n    SvErrRet B out v n0 ∨')])]
    names = [g.split(' : ', 1)[0].strip() for g in hyps]

    out = []
    O = out.append
    O(f"import C3BootProofs.Proofs.{SEG[0]}")
    O("import C3BootProofs.Proofs.SvOk")
    O("")
    O("/-!\n# `sigstore::verify` from 0x72 to its return\n\nWritten by `scripts/gen-sv-top.py` from "
      f"`{SEG[1]}` and `sv_ok_3264`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    for line in src.split('\n'):
        if line.startswith('open '):
            O(line)
            O("")
            break
    O("set_option maxHeartbeats 64000000 in")
    O("set_option maxRecDepth 100000 in")
    O("/-- **`sigstore::verify` from 0x72 to its return**: it returns `Err`, panics, or meets the success "
      "condition and returns `Ok`. -/")
    O(f"theorem sv_verify_72 {header}")
    O("\n".join(f"    ({g})" for g in hyps))
    O("    (hOk : SvOutOk B out) :")
    O("    SvErrRet B out v n0 ∨ Panics n0 ∨")
    O("    (" + " ∧\n      ".join(st.sc_parts) + " ∧")
    O(f"      SvOkRet B out v n0 ({vals['w3c']}) ({vals['w78']}) ({vals['r25']}) ({vals['r23']})) := by")
    O(f"  rcases {SEG[1]} {' '.join(names)} with e | e | hx")
    O("  · exact .inl e")
    O("  · exact .inr (.inl e)")
    got = nm + pats
    for x in got[:-1]:
        O(f"  obtain ⟨{x}, hx⟩ := hx")
    O(f"  have {got[-1]} := hx")
    ok = (f"sv_ok_3264 F {pat['E']} {pat['ST']} c1 (fun x hx => ({pat['FR']} x hx).trans (fM x hx).symm) {pat['V']} hret "
          f"{pat['r2']} {pat['r18']} hOk {pat['r3']} {pat['r4']} {pat['w3c']} {pat['w78']} {pat['r25']} {pat['r23']}")
    O(f"  exact .inr (.inr ⟨{', '.join(nm)}, {ok}⟩)")
    O("")
    O("end C3.RV32.Sv")
    O("")
    open('C3BootProofs/Proofs/SvTop.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    main()
