#!/usr/bin/env python3
"""Writes `SvVerify.lean`: `sigstore::verify` from its entry to its return.

`sv_pro` runs the prologue from the entry to 0x5C, and `sv_verify_5c` from
there to the return. `sv_verify` joins them. Its statement names the entry
machine `n`: the arguments are its registers, the saved registers are its
`s0..s11` and `ra`, and the frame words that `sv_verify_5c` reads at 0x5C
are those of the memory the prologue leaves, `svProMem`.

Usage: python3 scripts/gen-sv-entry.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import IDENT, Stage, groups, param_key, strip_parens, subst, top_split  # noqa: E402
from svseg import part_count  # noqa: E402

SRC = 'C3BootProofs/Proofs/SvTop.lean'
LP = "memLoad32 Me (reg n a1)"
LL = "memLoad32 Me (reg n a1 + 4)"
PM = f"svProMem Me B n ({LP}) ({LL})"
ARGS = {'out': "reg n a0", 'bp': "reg n a1", 'rootp': "reg n a2", 'dg': "reg n a3", 'lp': LP, 'll': LL,
        'v': "(fun k => reg n (savedReg k))", 'M0': "Me"}
# What sv_pro and the lemmas about svProMem give for sv_verify_5c's start.
START = {
    'FW': "FW", 'E0': "(E.fr F fM1)", 'V0': "(by rw [s1.mem]; exact svProMem_saves)", 's0': "(by rw [s1.mem]; exact s1)", 'M0': "Me",
    'fM': "fM1", 'g0_2': "sp1", 'g0_10': "(ra0.trans (by rw [BitVec.add_assoc]; rfl))",
    'g0_11': "(ra1.trans (by rw [BitVec.add_assoc]; rfl))", 'g0_18': "r18", 'g0_19': "r19", 'g0_20': "r20",
    'g0_21': "r21", 'g0_22': "r22", 'g0_26': "r26",
    'w0_360': "(by rw [s1.mem]; exact svProMem_reader.1)", 'w0_364': "(by rw [s1.mem]; exact svProMem_reader.2.1)",
    'w0_368': "(by rw [s1.mem]; exact svProMem_reader.2.2.1)",
    'w0_36c': "(by rw [s1.mem]; exact svProMem_reader.2.2.2)",
}


def names_of(part, start):
    """The names `obtain` gives a success condition's part."""
    out = []
    for piece in top_split(part, ' ∧ '):
        piece = piece.strip()
        while piece.startswith('∃ '):
            c = piece.index(',')
            out += piece[2:c].split(":")[0].split()
            piece = piece[c + 1:].strip()
        out.append(f"p{start + len(out)}")
    return out


def main():
    src = open(SRC).read()
    i = src.index('theorem sv_verify_5c ')
    stmt = src[i:src.index(':= by\n', i)]
    header = stmt.split('\n', 1)[0][len('theorem sv_verify_5c '):]
    binders = []
    for g in re.findall(r"\{([^}]*)\}", header):
        names, ty = g.rsplit(' : ', 1)
        binders += [(b, ty) for b in names.split()]
    hyps = []
    for g in groups(stmt[stmt.index('(FW : '):stmt.index('\n    SvErrRet B out v n0 ∨')]):
        p, t = g.split(' : ', 1)
        hyps.append((p.strip(), t.strip()))
    # Frame binders: a word, byte, or range of the frame at 0x5C that names a binder.
    env = dict(ARGS)
    frame = {}
    for p, t in hyps:
        key = param_key(p)
        if key and key[0] == 'w' and p not in START:
            m = re.fullmatch(r"memLoad32 n0\.mem (\(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x[0-9A-F]+\)) = (\w+)", t)
            if m and m.group(2) in dict(binders):
                env[m.group(2)] = f"memLoad32 ({PM}) {m.group(1)}"
                frame[p] = "(by rw [s1.mem])"
    kept = [(p, subst(t, env)) for p, t in hyps if p not in START and p not in frame]
    for p, t in kept:
        assert not re.search(IDENT.format("n0"), t), (p, t[:120])
    gone = set(ARGS) | {b for b in env if b not in ARGS} | {'n0'}
    bgroups = {}
    for b, ty in binders:
        if b not in gone:
            bgroups.setdefault(ty, []).append(b)
    new_binders = "{Me : Word → BitVec 8} {n : Machine} " + " ".join(
        "{" + " ".join(bs) + " : " + ty + "}" for ty, bs in bgroups.items())
    # The conclusion: sv_verify_5c's, about `n`.
    body = stmt[stmt.index('\n    SvErrRet B out v n0 ∨') + 1:].rstrip()
    lines = body.split('\n')
    sc_lines = lines[1:]
    sc_text = "\n".join(sc_lines)
    ok_at = sc_text.rindex("SvOkRet ")
    parts = [l.strip() for l in sc_text[:ok_at].split('\n') if l.strip()]
    parts[0] = parts[0][1:]
    parts = [x[:-2] if x.endswith(' ∧') else x for x in parts]
    ok = sc_text[ok_at:]
    ok = ok[:ok.rindex(')')] if ok.count(')') > ok.count('(') else ok
    names = []
    for part in parts:
        names += names_of(part, len(names))
    S = lambda t: re.sub(IDENT.format("n0"), "n", subst(t, env))

    out = []
    O = out.append
    O("import C3BootProofs.Proofs.SvEntry")
    O("")
    O("/-!\n# `sigstore::verify` from its entry to its return\n\nWritten by `scripts/gen-sv-entry.py` from "
      "`sv_pro` and `sv_verify_5c`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    for line in src.split('\n'):
        if line.startswith('open '):
            O(line + " C3.RV32.Dq C3.RV32.Pv" if "C3.RV32.Dq" not in line else line)
            O("")
            break
    O("set_option maxHeartbeats 64000000 in")
    O("set_option maxRecDepth 100000 in")
    O("/-- **`sigstore::verify`**: called with the bundle at `a1`, the trust root at `a2`, the artifact's "
      "digest at `a3`, and the result at `a0`, it returns `Err`, panics, or meets the success condition and "
      "returns `Ok`. -/")
    O(f"theorem sv_verify {new_binders}")
    O("    (C : CodeIn Me SV sigstoreVerifyCode) (E : SvCode Me) (FW : Fr (B + 0xFFFFEC10) 0x3A50)")
    O("    (s : St Me SV n 0 (reg n)) (rsp : reg n sp = B + 0x2660) (hb : (reg n a1).toNat % 4 = 0)")
    O("    (sb : Sep (reg n a1) 8 (B + BitVec.ofNat 32 0x262C) 0x34)")
    O("\n".join(f"    ({p} : {t})" for p, t in kept) + " :")
    O("    SvErrRet B (reg n a0) (fun k => reg n (savedReg k)) n ∨ Panics n ∨")
    O("    (" + " ∧\n      ".join(S(x) for x in parts) + " ∧")
    O(f"      {S(ok).replace('SvOkRet B out v n0', 'SvOkRet B (reg n a0) (fun k => reg n (savedReg k)) n')}) := by")
    O("  have F := sv_frW FW")
    O("  obtain ⟨n1, c1, s1, sp1, r18, r19, r21, r20, r26, r22, ra0, ra1, rk⟩ := sv_pro C F s rsp hb sb")
    O("  have fM1 : ∀ x, SvR B x → n1.mem x = Me x := fun x hx => by rw [s1.mem]; exact svProMem_out hx")
    O("  have hm : ∀ x, SvR B x → n1.mem x = n.mem x := fun x hx => by rw [fM1 x hx, s.mem]")
    args = " ".join(START.get(p) or frame.get(p) or p for p, _ in hyps)
    named = " ".join(f"({b} := {env[b]})" if b in env else f"({b} := {b})" for b, _ in binders
                     if b not in ('n0',))
    O(f"  rcases sv_verify_5c {named} (n0 := n1) {args} with e | e | hx")
    O("  · exact .inl (SvErrRet.pre c1 (rk _ (by decide)) (rk _ (by decide)) hm e)")
    O("  · exact .inr (.inl (Panics.of_steps c1 e))")
    for x in names:
        O(f"  obtain ⟨{x}, hx⟩ := hx")
    O("  refine .inr (.inr ?_)")
    for x in names:
        O(f"  refine ⟨{x}, ?_⟩")
    O("  exact SvOkRet.pre c1 (rk _ (by decide)) (rk _ (by decide)) hm hx")
    O("")
    O("end C3.RV32.Sv")
    O("")
    open('C3BootProofs/Proofs/SvVerify.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    main()
