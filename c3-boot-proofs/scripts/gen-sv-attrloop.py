#!/usr/bin/env python3
"""Writes `SvAttrLoop.lean`: the timestamp's signed attributes loop of
`sigstore::verify`, from its branch at 0xFF8 to the attributes' end at
0x10A4.

One iteration is the segment `sv_seg_attr` (`sv_trl`, `sv_tra`, then
`sv_trv`). It takes the next attribute off the slice (`cp`, `rem`), so
its new state depends on what it parsed; `sv_attrStep` is that step as a
relation, and `svChain` strings `k` of them together. The exit is
`sv_trx`, once `rem` is 0. The theorem is by induction on a bound on
`rem`, which every attribute (two bytes at least) lowers. It carries one
invariant besides the stages' hypotheses: the content-type flag is 0 or 1,
which `sv_trx` needs and `sv_trv` keeps.

Usage: python3 scripts/gen-sv-attrloop.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import IDENT, Chain, Stage, lean_binders, strip_parens, subst  # noqa: E402
from svloop import GLOBAL, Loop, invariants  # noqa: E402
from svmerge import paths_of, sc_pattern, split  # noqa: E402
from svseg import canon, strip_exists  # noqa: E402

BODY = ('SvSegAttr', 'sv_seg_attr')
EXIT = ('SvTrx', 'sv_trx')
NAME = 'sv_attrloop'
STEP = 'sv_attrStep'
OK = 'sv_attrloopOk'
TSAV = [('SvTrvct', 'sv_trvct'), ('SvTrvmd', 'sv_trvmd'), ('SvTrvother', 'sv_trvother')]


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
    assert loopv == ['dg', 'flag', 'cp', 'rem'], loopv
    groups_, seen = [], set(loopv) | {'n0'} | set(L.local)
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
    proj = {b: "s" + ".2" * j + (".1" if j + 1 < len(loopv) else "") for j, b in enumerate(loopv)}
    sc = " ∧ ".join(st.sc_parts)
    new = "(" + ", ".join(L.upd[b] for b in loopv) + ")"
    rel = subst(f"{proj['rem']} ≠ 0 ∧ " + (sc + " ∧ " if sc else "") + f"s' = {new}", proj)
    ok = subst(success_text(*EXIT), L.local)
    ok_k = re.sub(IDENT.format("n0"), "nk", subst(ok, dict(zip(loopv, ps))))
    T = "Word × Word × Word × Word"

    # The body's names, as the proof takes it apart.
    args = L.args({'hrem': 'hrem'})
    ch = Chain(lambda x: None)
    _, names1, pats1, _ = ch.call(st, {p: a for (p, _), a in zip(st.params, args)})
    proofs = ch.proofs
    tl_pf = next(nm for nm, piece in proofs
                 if re.fullmatch(r"derElement 0x30 \(memBytes M0 cp rem\.toNat\) = \.ok \w+", canon(strip_exists(piece))))
    tl = re.search(r"\.ok (\w+)$", canon(strip_exists(dict(proofs)[tl_pf]))).group(1)
    tl_local = names1[names1.index(tl_pf) - 1]
    flag_pf = next(nm for nm, piece in proofs if "trv_w7c" in piece and " ∨ " in piece)
    ov = {'FW': 'FW', 'hret': 'hret', 'hO': 'hO', 'M0': 'M0', 'E0': 'E1', 'V0': 'V1', 's0': 's1', 'fM': 'fR1'}
    for p, _ in L.per:
        ov[p] = p
    ov['cr_in'] = f"((cr_in).restW {tl_pf})"
    invs = invariants(L, proofs)
    for p, _, nm in invs:
        ov[p] = nm
    a2, _, _, _ = ch.call(st, ov)
    a2 = a2[len(a2) - len(st.params):]
    hn = [p for p, _ in head]
    per_names = [p for p, _ in L.kept_per if p != 'hrem']
    ih_args = [a for (p, _), a in zip(st.params, a2) if p in hn or p in per_names]

    out = []
    O = out.append
    O(f"import C3BootProofs.Proofs.SvSeg")
    O(f"import C3BootProofs.Proofs.{BODY[0]}")
    O(f"import C3BootProofs.Proofs.{EXIT[0]}")
    O("")
    O("/-!\n# `sigstore::verify`: the signed attributes loop\n\nWritten by `scripts/gen-sv-attrloop.py` from "
      f"`{BODY[1]}` and `{EXIT[1]}`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    O(L.opens())
    O("")
    O("/-- One more signed attribute, from state `s` to `s'` (`dg`, the content-type flag, and the attributes "
      "left): there are some, and the next one is well formed. -/")
    O(f"def {STEP} {explicit} (M0 : Word → BitVec 8) : {T} → {T} → Prop :=")
    O(f"  fun s s' => {rel}")
    O("")
    O(f"/-- How `{EXIT[1]}` ends once no attributes are left. -/")
    O(f"def {OK} {explicit} (M0 : Word → BitVec 8) ({' '.join(ps)} : Word) (nk : Machine) : Prop :=")
    O(f"  rem' = 0 ∧ " + "".join(f"({subst(t, dict(zip(loopv, ps)))}) ∧ " for _, t, _ in invs) + f"({ok_k})")
    O("")
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O("/-- The signed attributes loop: `k` more attributes, then the end. -/")
    O(f"theorem {NAME} {fixed}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL) + " :")
    O("    ∀ (N : Nat) {dg flag cp rem : Word} {n0 : Machine},")
    O("    (hN : rem.toNat ≤ N) → (hflag : flag = 0 ∨ flag = 1) →")
    for p, t in head:
        O(f"    ({p} : {t}) →")
    for p, t in L.kept_per:
        if p != 'hrem':
            O(f"    ({p} : {t}) →")
    O(f"    SvErrRet B out v n0 ∨ ∃ k {' '.join(ps)}, svChain ({STEP} {fixed_names} M0) k {tup} {ptup} ∧")
    O("      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧")
    O(f"      SvKeepL B n0.mem nk.mem {L.kl} ∧ {OK} {fixed_names} M0 {' '.join(ps)} nk := by")
    xnamed = " ".join(f"({b} := {L.local.get(b, b)})" for names, _ in lean_binders(*EXIT) for b in names)
    dead = {p for p, t in X.params if strip_parens(t.split(' = ')[-1]) in L.local}
    xargs = " ".join({'hrem': 'h0', 'hflag': 'hflag'}.get(p, 'rfl' if p in dead else p) for p, _ in X.params)
    intro = f"intro {' '.join(loopv)} n0 hN hflag {' '.join(hn)} {' '.join(per_names)}"
    exit_ok = (f"exact .inr ⟨0, {', '.join(loopv)}, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), "
               f"h0, {''.join(p + ', ' for p, _, _ in invs)}okx⟩")
    O("  intro N")
    O("  induction N with")
    O("  | zero =>")
    O(f"    {intro}")
    O("    have h0 : rem = 0 := svRem_zero hN")
    O(f"    rcases {EXIT[1]} {xnamed} {xargs} with ⟨-, e⟩ | okx")
    O("    · exact .inl e")
    O(f"    · {exit_ok}")
    O("  | succ N ih =>")
    O(f"    {intro}")
    O("    by_cases h0 : rem = 0")
    O(f"    · rcases {EXIT[1]} {xnamed} {xargs} with ⟨-, e⟩ | okx")
    O("      · exact .inl e")
    O(f"      · {exit_ok}")
    O(f"    rcases {BODY[1]} {L.named()} {' '.join(a if a != 'hrem' else 'h0' for a in args)} with e | "
      f"⟨{', '.join(names1 + pats1)}⟩")
    O("    · exact .inl e")
    O(f"    have hdec := svRem_le (a := {tl_local}.header + {tl_local}.len) (N := N) "
      f"(by have := derElement_header {tl_pf}; omega)")
    O(f"      (by have := derElement_bound {tl_pf}; rw [memBytes_length] at this; exact this) hN")
    ws = list(dict.fromkeys(re.findall(r"\btrv_w\w+", dict(proofs)[flag_pf])))
    es = [f"e{j}" for j in range(len(ws))]
    ef = es[next(j for j, w in enumerate(ws) if "w7c" in w)]
    pats = []
    paths = paths_of(split([Stage(*v) for v in TSAV], []))
    for vf, vn in TSAV:
        st_v = Stage(vf, vn)
        nm = [f"pc{i}'" for i in range(len(paths[st_v.name]))] + [f"{x}'" for x in sc_pattern(st_v)]
        pats.append("⟨" + ", ".join(nm + es) + "⟩")
    w78 = next(x for x in names1 if "trv_w7c" in x)
    O(f"    have hflag' : {w78} = 0 ∨ {w78} = 1 := by")
    O(f"      rcases {flag_pf} with {' | '.join(pats)}")
    O(f"      · exact .inr {ef}")
    O(f"      · rw [{ef}]; exact hflag")
    O(f"      · rw [{ef}]; exact hflag")
    O(f"    rcases ih hdec hflag' {' '.join(ih_args)} with e | ⟨k, {', '.join(ps)}, chn, nk, cs, h3, h4, hk, okk⟩")
    O("    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)")
    O(f"    · exact .inr ⟨k + 1, {', '.join(ps)}, svChain.cons ⟨h0, {', '.join(names1)}, rfl⟩ chn, nk, c1.trans cs, "
      "h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩")
    O("")
    # The loop as a stage.
    pr = dict(zip(loopv, ps))
    facts, dropped = [], []
    for f in X.facts:
        if f.key == 'STEPS':
            continue
        if f.key.startswith('r') and f.rhs is not None and strip_parens(f.rhs) in L.local:
            dropped.append(f.key)
            continue
        t = subst(subst(f.text, L.local), pr)
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
    O(f"theorem {NAME}_st {fixed} {{N : Nat}} {{dg flag cp rem : Word}} {{n0 : Machine}}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL))
    O("    (hN : rem.toNat ≤ N) (hflag : flag = 0 ∨ flag = 1)")
    for p, t in head:
        O(f"    ({p} : {t})")
    for p, t in L.kept_per:
        if p != 'hrem':
            O(f"    ({p} : {t})")
    O("    :")
    O("    SvErrRet B out v n0 ∨")
    O(f"    (∃ k {' '.join(ps)}, svChain ({STEP} {fixed_names} M0) k {tup} {ptup} ∧")
    O("      rem' = 0 ∧" + "".join(f" ({subst(t, pr)}) ∧" for _, t, _ in invs) +
      ("" if not X.sc_parts else "\n      " + " ∧ ".join(subst(subst(x, L.local), pr) for x in X.sc_parts) + " ∧"))
    O("    ∃ n', Steps n0 n' ∧")
    O("        " + " ∧\n        ".join(t for _, t in facts) + ") := by")
    O(f"  rcases {NAME} FW hret hO M0 N hN hflag {' '.join(hn)} {' '.join(per_names)} with e | "
      f"⟨k, {', '.join(ps)}, chn, nk, cs, hr3, hr4, hkl, okh⟩")
    O("  · exact .inl e")
    iv = [f"iv{j}" for j in range(len(invs))]
    fnames = [f"f_{f.key}" if f.key not in dropped else "-" for f in X.facts if f.key != 'STEPS']
    O(f"  obtain ⟨hz, {', '.join(iv + xnm + ['n1', 'cn'] + fnames)}⟩ := okh")
    terms = [{"r3": "f_r3.trans hr3", "r4": "f_r4.trans hr4", "KL": "(hkl.trans f_KL).mono (by decide)"}.get(k, f"f_{k}")
             for k, _ in facts]
    O(f"  exact .inr ⟨k, {', '.join(ps)}, chn, hz, {', '.join(iv + xnm + ['n1', 'cs.trans cn'] + terms)}⟩")
    O("")
    O("end C3.RV32.Sv")
    O("")
    open('C3BootProofs/Proofs/SvAttrLoop.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    main()
