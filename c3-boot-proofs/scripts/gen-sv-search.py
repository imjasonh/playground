#!/usr/bin/env python3
"""Writes the search theorems of `sigstore::verify`: a loop over `N` entries
whose body is a generated stage for an entry that doesn't match (`miss`),
with a stage for one that does (`hit`) and one for the end of the entries
(`end`), which returns an error.

The count of bytes left is nonzero before each of the `N` entries and zero
after them. The theorem is by induction on `N`: the run returns an error, or
there is an entry `k < N` that matches, after `k` that don't, and the run
reaches the end of `hit` from entry `k`. `hit`'s success condition and
facts are kept whole, at the machine where entry `k` starts; the theorem
relates that machine to the start.

Usage: python3 scripts/gen-sv-search.py [name ...]   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import DEFAULTS, IDENT, Chain, Stage, lean_binders, strip_parens, subst, top_split  # noqa: E402
from svloop import GLOBAL, Loop  # noqa: E402

# file: (theorem, miss, hit, end, doc)
SEARCHES = {
    'SvISearch': ('sv_isearch', ('SvImiss', 'sv_imiss'), ('SvIhit', 'sv_ihit'), ('SvIend', 'sv_iend'),
                  "the search of the root's Fulcio intermediates for the leaf's issuer"),
    'SvTSearch': ('sv_tsearch', ('SvTlmiss', 'sv_tlmiss'), ('SvTlhit', 'sv_tlhit'), ('SvTlend', 'sv_tlend'),
                  "the search of the root's TSAs for the timestamp's signer"),
    'SvCSearch': ('sv_csearch', ('SvClmiss', 'sv_clmiss'), ('SvClhit', 'sv_clhit'), ('SvClend', 'sv_clend'),
                  "the search of the root's logs for the checkpoint's origin"),
}


def success_text(sfile, sname):
    """The success branch of a stage's conclusion, as written."""
    src = open(f'C3BootProofs/Proofs/{sfile}.lean').read()
    i = src.index(f'theorem {sname} ')
    j = src.index(':= by\n', i)
    st = src[i:j]
    k = st.index('\n    (¬')
    rest = st[k:].split('\n', 2)[2]
    return rest.strip()[:-1] if rest.strip().endswith(')') and rest.strip().count(')') > rest.strip().count('(') \
        else rest.strip()


def write(fname):
    name, (mf, mn), (hf, hn_), (ef, en), doc = SEARCHES[fname]
    L = Loop(mf, mn)
    H = Stage(hf, hn_)
    E = Stage(ef, en)
    st, head, loopv = L.st, L.head, L.loopv
    hm = dict(H.params)['hm']
    cond = [(p, t) for p, t in L.kept_per if p == 'hc']
    assert cond, "no `hc` in the miss stage"
    cnt = strip_parens(top_split(cond[0][1], ' ≠ ')[0])
    valid = [(p, t) for p, t in L.kept_per if p != 'hm']
    ps = list(L.prime.values())
    tup = L.tup()
    hn = [p for p, _ in head]
    ok = success_text(hf, hn_)
    ok_k = re.sub(IDENT.format("n0"), "nk", L.primed(ok))
    Doc = doc[0].upper() + doc[1:]
    out = []
    O = out.append
    O("import C3BootProofs.Proofs.SvSeg")
    for f in (mf, hf, ef):
        O(f"import C3BootProofs.Proofs.{f}")
    O("")
    O(f"/-!\n# `sigstore::verify`: {Doc}\n\nWritten by `scripts/gen-sv-search.py` from `{mn}`, `{hn_}`, and `{en}`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    O(L.opens())
    O("")
    for names, ty in lean_binders(hf, hn_) + lean_binders(mf, mn):
        more = [b for b in names if b not in L.bset and b not in L.upd and b not in L.local and b != 'n0']
        if more:
            L.fixed.append("{" + " ".join(more) + " : " + ty + "}")
            L.bset |= set(more)
    fixed_names = [b for g in L.fixed for b in g[1:g.rindex(' : ')].split()]
    okname = f"{name}Ok"
    O(f"/-- How `{hn_}` ends from the entry that matches: its success condition, then the state at its end. -/")
    explicit = " ".join("(" + g[1:-1] + ")" for g in L.fixed)
    O(f"def {okname} {explicit} (M0 : Word → BitVec 8) ({' '.join(ps)} : Word) (nk : Machine) : Prop :=")
    O(f"  {ok_k}")
    O("")
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O(f"/-- {Doc}. -/")
    O(f"theorem {name} {' '.join(L.fixed)}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL) + " :")
    O(f"    ∀ (N : Nat) {{{' '.join(loopv)} : Word}} {{n0 : Machine}},")
    O(f"    (hz : ∀ {' '.join(ps)}, {L.peq('N')} → {cnt}' = 0) →")
    for p, t in head:
        O(f"    ({p} : {t}) →")
    vtext = " ∧ ".join(f"({L.primed(t)})" for _, t in valid) or "True"
    O(f"    (∀ i, i < N → ∀ {' '.join(ps)}, {L.peq('i')} → {vtext}) →")
    O("    SvErrRet B out v n0 ∨ ∃ k, k < N ∧")
    O(f"      (∀ i, i < k → ∀ {' '.join(ps)}, {L.peq('i')} → ¬ ({L.primed(hm)})) ∧")
    O(f"      ∃ {' '.join(ps)}, {L.peq('k')} ∧")
    O("      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧")
    O(f"      SvKeepL B n0.mem nk.mem {L.kl} ∧")
    O(f"      {okname} {' '.join(fixed_names)} M0 {' '.join(ps)} nk := by")
    O("  intro N")
    O("  induction N with")
    O("  | zero =>")
    O(f"    intro {' '.join(loopv)} n0 hz {' '.join(hn)} _")
    eargs = []
    for p, t in E.params:
        if p == 'hc':
            eargs.append(f"(hz {' '.join(loopv)} (svIter_zero _ {tup}).symm)")
        else:
            eargs.append("rfl" if (p, t) in L.per and (p, t) not in L.kept_per else p)
    ch = Chain(lambda x: None)
    _, enames, _, _ = ch.call(E, {p: a for (p, _), a in zip(E.params, eargs)})
    used = " ".join(t for _, t in E.params)
    edef = " ".join(f"({b} := {DEFAULTS[ty]})" for b, ty in E.binders
                    if b in L.local and not re.search(IDENT.format(re.escape(b)), used))
    O(f"    rcases {en} {L.named()} {edef} {' '.join(eargs)} with ⟨-, e⟩ | ⟨{', '.join(enames)}, -⟩")
    O("    · exact .inl e")
    O(f"    · exact {enames[0]}.elim")
    O("  | succ N ih =>")
    O(f"    intro {' '.join(loopv)} n0 hz {' '.join(hn)} H")
    if valid:
        O(f"    obtain ⟨{', '.join(p for p, _ in valid)}⟩ := H 0 (Nat.succ_pos N) {' '.join(loopv)} "
          f"(svIter_zero _ {tup}).symm")
    else:
        O("    have _ := H")
    O(f"    by_cases hm : {subst(hm, L.local)}")
    hargs = []
    for p, t in H.params:
        hargs.append("rfl" if (p, t) in L.per and (p, t) not in L.kept_per else p)
    O(f"    · rcases {hn_} {L.named()} {' '.join(hargs)} with ⟨-, e⟩ | okh")
    O("      · exact .inl e")
    O(f"      · exact .inr ⟨0, Nat.succ_pos N, fun i hi => absurd hi (Nat.not_lt_zero i), {', '.join(loopv)}, "
      f"(svIter_zero _ {tup}).symm, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), okh⟩")
    args = L.args()
    ch = Chain(lambda x: None)
    _, names1, pats1, _ = ch.call(st, {p: a for (p, _), a in zip(st.params, args)})
    O(f"    rcases {mn} {L.named()} {' '.join(args)} with ⟨-, e⟩ | ⟨{', '.join(names1 + pats1)}⟩")
    O("    · exact .inl e")
    ov = {'F': 'F', 'hret': 'hret', 'hO': 'hO', 'M0': 'M0', 'E0': 'E1', 'V0': 'V1', 's0': 's1', 'fM': 'fR1'}
    for p, _ in L.per:
        ov[p] = p
    a2, _, _, _ = ch.call(st, ov)
    a2 = a2[len(a2) - len(st.params):]
    hargs2 = [a for (p, _), a in zip(st.params, a2) if p in hn]
    vs = " ".join(ps)
    O(f"    rcases ih (fun {vs} e0 => hz {vs} (e0.trans (svIter_succ _ N {tup}).symm)) {' '.join(hargs2)}"
      f" (fun i hi {vs} e0 => H (i + 1) (Nat.succ_lt_succ hi) {vs} (e0.trans (svIter_succ _ i {tup}).symm))"
      f" with e | ⟨k, hk, hn, {', '.join(ps)}, e0, nk, cs, h3, h4, hkl, okh⟩")
    O("    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)")
    O(f"    · refine .inr ⟨k + 1, by omega, fun i hi {vs} e1 => ?_, {', '.join(ps)}, "
      f"(e0.trans (svIter_succ _ k {tup}).symm), nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, "
      "(K1_L.trans hkl).mono (by decide), okh⟩")
    O("      cases i with")
    O(f"      | zero => cases e1.trans (svIter_zero _ {tup}); exact hm")
    O(f"      | succ i => exact hn i (by omega) {vs} (e1.trans (svIter_succ _ i {tup}))")
    O("")
    O("end C3.RV32.Sv")
    O("")
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    for f in sys.argv[1:] or SEARCHES:
        write(f)
