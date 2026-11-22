#!/usr/bin/env python3
"""Writes `SvP256St.lean`: `sv_p256` in the form the composed stages use.

`sv_p256` states the P-256 check's success condition with its witnesses
nested around a last comparison whose failure returns an error, names the
machine at its end `m'`, and states the frame words it keeps as reads of
the start's memory. `sv_p256_st` states the same success condition as one
condition per line, the end machine as `n'`, those frame words with
binders, and a `SvKeepL` that covers the whole frame.

Usage: python3 scripts/gen-sv-p256st.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import groups, top_split  # noqa: E402

SRC = 'C3BootProofs/Proofs/SvP256All.lean'
FA = "B + 0x21A0 + BitVec.ofNat 32"
DG = f"memLoad32 n0.mem ({FA} 0x84)"
FUN = re.compile(r"\(\(\(fun e => memLoad32 n0\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 e\)\)\) (0x[0-9A-F]+)\)")


def names_of(part):
    """The names `rcases` gives a success condition's line, as `Chain` does."""
    out = []
    for piece in top_split(part, ' ∧ '):
        piece = piece.strip()
        while piece.startswith('∃ '):
            c = piece.index(',')
            out += piece[2:c].split()
            piece = piece[c + 1:].strip()
        out.append(None)
    return out


def main():
    src = open(SRC).read()
    i = src.index('theorem sv_p256 ')
    stmt = src[i:src.index(':= by\n', i)]
    lines = stmt.split('\n')
    k = next(j for j, l in enumerate(lines) if l.startswith('    (¬ '))
    header, params = lines[0], lines[1:k]
    params[-1] = params[-1].rstrip()
    assert params[-1].endswith(' :')
    params[-1] = params[-1][:-2]
    body = lines[k:]
    # The success condition: the first condition, the witnesses' lines, and the last comparison.
    sc1 = body[1].strip()
    assert sc1.startswith('(') and sc1.endswith(' ∧')
    sc1 = sc1[1:-2]
    j = next(n for n, l in enumerate(body) if l.strip().startswith('((¬ ('))
    mids = [l.strip()[:-2] for l in body[2:j]]
    neg = body[j].strip()
    assert neg.endswith(' ∧ SvErrRet B out v n0) ∨')
    sc2 = neg[len('((¬ '):-len(' ∧ SvErrRet B out v n0) ∨')]
    last = body[j + 1].strip()
    cut = last.index(" ∧ ∃ m', Steps n0 m' ∧ ")
    assert last[1:cut] == sc2, (last[1:cut][:80], sc2[:80])
    facts = [last[cut + len(" ∧ ∃ m', Steps n0 m' ∧ "):]] + [l.strip() for l in body[j + 2:]]
    text = " ".join(facts).rstrip()
    while text.endswith(')') and text.count(')') > text.count('('):
        text = text[:-1]
    facts = [f.strip() for f in top_split(text, ' ∧ ')]
    # Frame words the check keeps, as binders.
    kept = []
    out_facts = []
    for f in facts:
        m = FUN.search(f)
        if m:
            e = int(m.group(1), 16)
            kept.append(e)
            f = FUN.sub(f"w{e:x}", f)
        out_facts.append(f.replace("m'", "n'"))
    out_facts.append("SvKeepL B n0.mem n'.mem [(0x0, 0x1690)]")
    terms = []
    for f, n in zip(facts, range(len(facts))):
        m = FUN.search(f)
        terms.append(f"f{n}.trans w0_{int(m.group(1), 16):x}" if m else f"f{n}")
    terms.append("SvKeepL.whole")
    # Binders and hypotheses.
    binders = header[len('theorem sv_p256 '):]
    ws = " ".join(f"w{e:x}" for e in [0x84] + kept)
    binders = binders.replace("{er es : Bytes}", "{" + ws + " : Word} {er es : Bytes}", 1)
    new_params = []
    for p in params:
        p = p.replace(f"(dg_in : SvIn B ({DG}) 32)", f"(w0_84 : {DG} = w84) (dg_in : SvIn B w84 32)")
        new_params.append(p)
    new_params.append("    " + " ".join(f"(w0_{e:x} : memLoad32 n0.mem ({FA} 0x{e:X}) = w{e:x})" for e in kept))
    args = []
    for g in groups("\n".join(params)):
        nm = g.split(' : ', 1)[0].strip()
        args.append("(by rw [w0_84]; exact dg_in)" if nm == 'dg_in' else nm)
    named = " ".join(f"({b} := {b})" for b in re.findall(r"\{([^}]*) : Word\}", header)[0].split())
    # The success condition's names.
    pre = []
    for part in mids:
        for x in names_of(part):
            pre.append(x or f"a{len(pre)}")
    fin = [f"f{n}" for n in range(len(facts))]

    out = []
    O = out.append
    O("import C3BootProofs.Proofs.SvP256All")
    O("")
    O("/-!\n# `sigstore::verify`: the P-256 check, as a stage\n\nWritten by `scripts/gen-sv-p256st.py` from "
      "`sv_p256`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    for line in src.split('\n'):
        if line.startswith('open '):
            O(line)
            O("")
            break
    O("/-- A frame range that covers the whole frame keeps nothing. -/")
    O("theorem SvKeepL.whole {B : Word} {M M' : Word → BitVec 8} : SvKeepL B M M' [(0x0, 0x1690)] :=")
    O("  fun e he h => by have := h (0x0, 0x1690) (List.mem_singleton.mpr rfl); simp only at this; omega")
    O("")
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O("/-- **The P-256 check, as a stage**: `sv_p256` from 0xFBA to 0x2034. -/")
    O(f"theorem sv_p256_st {binders}")
    O("\n".join(new_params) + " :")
    O("    SvErrRet B out v n0 ∨ Panics n0 ∨")
    O(f"    ({sc1} ∧")
    for part in mids:
        O(f"      {part} ∧")
    O(f"      {sc2} ∧")
    O("    ∃ n', Steps n0 n' ∧")
    O("        " + " ∧\n        ".join(out_facts) + ") := by")
    O(f"  rcases sv_p256 {named} {' '.join(args)} with ⟨-, e⟩ | e | ⟨h1, {', '.join(pre)}, hfin⟩")
    O("  · exact .inl e")
    O("  · exact .inr (.inl e)")
    O(f"  rcases hfin with ⟨-, e⟩ | ⟨h2, n1, c1, {', '.join(fin)}⟩")
    O("  · exact .inl e")
    O(f"  exact .inr (.inr ⟨h1, {', '.join(pre)}, h2, n1, c1, {', '.join(terms)}⟩)")
    O("")
    O("end C3.RV32.Sv")
    O("")
    open('C3BootProofs/Proofs/SvP256St.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    main()
