#!/usr/bin/env python3
"""Writes `SvCosigLoop.lean`: the checkpoint's signature loop of
`sigstore::verify`, from its head at 0x2D6E to the signatures' end at
0x2F5A.

One iteration is the segment `sv_seg_cosig` (`sv_csa`, the space search, the
base64 groups, and the line's end). It takes the next line off the slice
(`w38`, `w5c`), so its new state depends on what it parsed; `sv_cosigStep`
is that step as a relation, and `svChain` strings `k` of them together.
The state includes the signature found so far, `sg`. The exit is `sv_csx`,
once `w5c` is 0. The theorem is by induction on a bound on `w5c`, which
every line (its newline at least) lowers.

Usage: python3 scripts/gen-sv-cosigloop.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import IDENT, Chain, Stage, lean_binders, subst  # noqa: E402
from svloop import GLOBAL, Loop  # noqa: E402
from svmerge import sc_pattern  # noqa: E402
from svseg import canon, strip_exists  # noqa: E402

BODY = ('SvSegCosig', 'sv_seg_cosig')
EXIT = ('SvCsx', 'sv_csx')
NAME = 'sv_cosigloop'
STEP = 'sv_cosigStep'
OK = 'sv_cosigloopOk'
FUEL = 'w5c'


def success_text(sfile, sname):
    src = open(f'C3BootProofs/Proofs/{sfile}.lean').read()
    i = src.index(f'theorem {sname} ')
    st = src[i:src.index(':= by\n', i)]
    rest = st[st.index('\n    (¬'):].split('\n', 2)[2].strip()
    return rest[:-1] if rest.count(')') > rest.count('(') else rest


def main():
    L = Loop(*BODY)
    X = Stage(*EXIT)
    st, head, loopv = L.st, L.head, L.loopv
    groups_, seen = [], set(loopv) | {'n0'}
    for names, ty in lean_binders(*BODY) + lean_binders(*EXIT):
        new = [b for b in names if b not in seen]
        seen |= set(new)
        if new:
            groups_.append((new, ty))
    fixed = " ".join("{" + " ".join(n) + " : " + t + "}" for n, t in groups_)
    explicit = " ".join("(" + " ".join(n) + " : " + t + ")" for n, t in groups_)
    fixed_names = " ".join(b for n, _ in groups_ for b in n)
    tup = "(" + ", ".join(loopv) + ")"
    ps = [b + "'" for b in loopv]
    ptup = "(" + ", ".join(ps) + ")"
    T = " × ".join(L.types[b] for b in loopv)
    proj = {b: "s" + ".2" * j + (".1" if j + 1 < len(loopv) else "") for j, b in enumerate(loopv)}
    sc = " ∧ ".join(st.sc_parts)
    new = "(" + ", ".join(L.upd[b] for b in loopv) + ")"
    rel = subst(f"{proj[FUEL]} ≠ 0 ∧ " + (sc + " ∧ " if sc else "") + f"s' = {new}", proj)
    ok = success_text(*EXIT)
    ok_k = re.sub(IDENT.format("n0"), "nk", subst(ok, dict(zip(loopv, ps))))
    typed_ps = " ".join(f"({p} : {L.types[b]})" for b, p in zip(loopv, ps))

    # The body's names, as the proof takes it apart.
    args = L.args({'hrem': 'h0'})
    ch = Chain(lambda x: None)
    _, names1, pats1, _ = ch.call(st, {p: a for (p, _), a in zip(st.params, args)})
    proofs = ch.proofs
    nl_pf = next(nm for nm, piece in proofs if re.fullmatch(r"nlScan M0 w38 0 w5c\.toNat = some \w+",
                                                            canon(strip_exists(piece))))
    ix = names1[names1.index(nl_pf) - 1]
    ov = {'F': 'F', 'hret': 'hret', 'hO': 'hO', 'M0': 'M0', 'E0': 'E1', 'V0': 'V1', 's0': 's1', 'fM': 'fR1'}
    for p, _ in L.per:
        ov[p] = p
    ov['sg_in'] = (f"(by rw [svSubOfNat_toNat (by have := (nlScan_lt _ _ _ {nl_pf}).2; omega)]; "
                   f"exact (sg_in).nlRest {nl_pf})")
    a2, _, _, _ = ch.call(st, ov)
    a2 = a2[len(a2) - len(st.params):]
    hn = [p for p, _ in head]
    per_names = [p for p, _ in L.kept_per if p != 'hrem']
    ih_args = [a for (p, _), a in zip(st.params, a2) if p in hn or p in per_names]
    bp = dict(st.params)
    xextra = [(p, t) for p, t in X.params if p not in bp and p != 'hrem0']
    ih_args += [p for p, _ in xextra]

    out = []
    O = out.append
    O("import C3BootProofs.Proofs.SvSegCk")
    O(f"import C3BootProofs.Proofs.{BODY[0]}")
    O(f"import C3BootProofs.Proofs.{EXIT[0]}")
    O("")
    O("/-!\n# `sigstore::verify`: the checkpoint's signature loop\n\nWritten by `scripts/gen-sv-cosigloop.py` from "
      f"`{BODY[1]}` and `{EXIT[1]}`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    O(L.opens())
    O("")
    O("/-- One more signature line, from state `s` to `s'`: there are bytes left, and the next line is well "
      "formed. -/")
    O(f"def {STEP} {explicit} (M0 : Word → BitVec 8) : {T} → {T} → Prop :=")
    O(f"  fun s s' => {rel}")
    O("")
    O(f"/-- How `{EXIT[1]}` ends once no lines are left. -/")
    O(f"def {OK} {explicit} (M0 : Word → BitVec 8) {typed_ps} (nk : Machine) : Prop :=")
    O(f"  {FUEL}' = 0 ∧ ({ok_k})")
    O("")
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O("/-- The checkpoint's signature loop: `k` more lines, then the end. -/")
    O(f"theorem {NAME} {fixed}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL) + " :")
    O(f"    ∀ (N : Nat) " + " ".join(f"{{{b} : {L.types[b]}}}" for b in loopv) + " {n0 : Machine},")
    O(f"    (hN : {FUEL}.toNat ≤ N) →")
    for p, t in head:
        O(f"    ({p} : {t}) →")
    for p, t in L.kept_per:
        if p != 'hrem':
            O(f"    ({p} : {t}) →")
    for p, t in xextra:
        O(f"    ({p} : {t}) →")
    O(f"    SvErrRet B out v n0 ∨ ∃ k {' '.join(ps)}, svChain ({STEP} {fixed_names} M0) k {tup} {ptup} ∧")
    O("      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧")
    O(f"      SvKeepL B n0.mem nk.mem {L.kl} ∧ {OK} {fixed_names} M0 {' '.join(ps)} nk := by")
    xnamed = " ".join(f"({b} := {b})" for b in dict.fromkeys(b for names, _ in lean_binders(*EXIT) for b in names))
    xargs = " ".join({'hrem0': 'h0'}.get(p, p) for p, _ in X.params)
    intro = f"intro {' '.join(loopv)} n0 hN {' '.join(hn)} {' '.join(per_names)} {' '.join(p for p, _ in xextra)}"
    exit_ok = (f"exact .inr ⟨0, {', '.join(loopv)}, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), "
               "h0, okx⟩")
    O("  intro N")
    O("  induction N with")
    O("  | zero =>")
    O(f"    {intro}")
    O(f"    have h0 : {FUEL} = 0 := svRem_zero hN")
    O(f"    rcases {EXIT[1]} {xnamed} {xargs} with {X.errpat} | okx")
    O("    · exact .inl e")
    O(f"    · {exit_ok}")
    O("  | succ N ih =>")
    O(f"    {intro}")
    O(f"    by_cases h0 : {FUEL} = 0")
    O(f"    · rcases {EXIT[1]} {xnamed} {xargs} with {X.errpat} | okx")
    O("      · exact .inl e")
    O(f"      · {exit_ok}")
    O(f"    rcases {BODY[1]} {L.named()} {' '.join(args)} with {st.errpat} | ⟨{', '.join(names1 + pats1)}⟩")
    O("    · exact .inl e")
    O(f"    have hdec := svRem_le1 (a := {ix} + 1) (N := N) (by omega) "
      f"(by have := (nlScan_lt _ _ _ {nl_pf}).2; omega) hN")
    O(f"    rcases ih hdec {' '.join(ih_args)} with e | ⟨k, {', '.join(ps)}, chn, nk, cs, h3, h4, hk, okk⟩")
    O("    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)")
    O(f"    · exact .inr ⟨k + 1, {', '.join(ps)}, svChain.cons ⟨h0, {', '.join(names1)}, rfl⟩ chn, nk, c1.trans cs, "
      "h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩")
    O("")
    # The loop as a stage.
    pr = dict(zip(loopv, ps))
    facts = []
    for f in X.facts:
        if f.key == 'STEPS':
            continue
        t = subst(f.text, pr)
        if f.key in ('r3', 'r4'):
            t = f"reg n' ({f.key[1]} : Fin 32) = reg n0 ({f.key[1]} : Fin 32)"
        elif f.key == 'KL':
            u = list(dict.fromkeys(re.findall(r"\(0x[0-9A-F]+, 0x[0-9A-F]+\)", L.kl + f.text)))
            t = "SvKeepL B n0.mem n'.mem [" + ", ".join(u) + "]"
        facts.append((f.key, f"({t})" if t.startswith('∀') else t))
    xnm = sc_pattern(X)
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O(f"/-- `{NAME}` as a stage. -/")
    O(f"theorem {NAME}_st {fixed} {{N : Nat}} " + " ".join(f"{{{b} : {L.types[b]}}}" for b in loopv) +
      " {n0 : Machine}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL))
    O(f"    (hN : {FUEL}.toNat ≤ N)")
    for p, t in head:
        O(f"    ({p} : {t})")
    for p, t in L.kept_per:
        if p != 'hrem':
            O(f"    ({p} : {t})")
    for p, t in xextra:
        O(f"    ({p} : {t})")
    O("    :")
    O("    SvErrRet B out v n0 ∨")
    O(f"    (∃ k {' '.join(ps)}, svChain ({STEP} {fixed_names} M0) k {tup} {ptup} ∧")
    O(f"      {FUEL}' = 0 ∧" + ("" if not X.sc_parts else "\n      " + " ∧ ".join(subst(x, pr) for x in X.sc_parts) + " ∧"))
    O("    ∃ n', Steps n0 n' ∧")
    O("        " + " ∧\n        ".join(t for _, t in facts) + ") := by")
    named = " ".join(f"({b} := {b})" for n, _ in groups_ for b in n)
    O(f"  rcases {NAME} {named} F hret hO M0 N hN {' '.join(hn)} {' '.join(per_names)} {' '.join(p for p, _ in xextra)} with e | "
      f"⟨k, {', '.join(ps)}, chn, nk, cs, hr3, hr4, hkl, okh⟩")
    O("  · exact .inl e")
    O(f"  obtain ⟨hz, {', '.join(xnm + ['n1', 'cn'] + [f'f_{k}' for k, _ in facts])}⟩ := okh")
    terms = [{"r3": "f_r3.trans hr3", "r4": "f_r4.trans hr4", "KL": "(hkl.trans f_KL).mono (by decide)"}.get(k, f"f_{k}")
             for k, _ in facts]
    O(f"  exact .inr ⟨k, {', '.join(ps)}, chn, hz, {', '.join(xnm + ['n1', 'cs.trans cn'] + terms)}⟩")
    O("")
    O("end C3.RV32.Sv")
    O("")
    open('C3BootProofs/Proofs/SvCosigLoop.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    main()
