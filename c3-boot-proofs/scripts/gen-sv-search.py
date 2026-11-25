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
from svmerge import sc_pattern  # noqa: E402

# Searches that scan a slice a byte at a time, counting up from 0: file:
# (count, base, length). Each iteration reads the byte at base + count, and
# the scan ends when count + 1 is the length.
RUNS = {'SvNSearch': ('ni', 'np', 'nl')}
RUNS_BOUND = {'sv_nsearch': '(nl.toNat - 1)'}

# file: (theorem, miss, hit, end, doc)
SEARCHES = {
    'SvISearch': ('sv_isearch', ('SvImiss', 'sv_imiss'), ('SvIhit', 'sv_ihit'), ('SvIend', 'sv_iend'),
                  "the search of the root's Fulcio intermediates for the leaf's issuer"),
    'SvTSearch': ('sv_tsearch', ('SvTlmiss', 'sv_tlmiss'), ('SvTlhit', 'sv_tlhit'), ('SvTlend', 'sv_tlend'),
                  "the search of the root's TSAs for the timestamp's signer"),
    'SvCSearch': ('sv_csearch', ('SvClmiss', 'sv_clmiss'), ('SvClhit', 'sv_clhit'), ('SvClend', 'sv_clend'),
                  "the search of the root's logs for the checkpoint's origin"),
    'SvNSearch': ('sv_nsearch', ('SvCnm', 'sv_cnm'), ('SvCns', 'sv_cns'), ('SvCne', 'sv_cne'),
                  "the search of a signature line for the space after the signer's name",
                  {'cond': 'hne', 'end': 'heq', 'match': 'hsp', 'reads': True}),
}


def bind(ps):
    """A tactic head that names each of a conjunction's parts."""
    if len(ps) == 1:
        return f"have {ps[0][0]}"
    return f"obtain ⟨{', '.join(p for p, _ in ps)}⟩"


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
    name, (mf, mn), (hf, hn_), (ef, en), doc, *more = SEARCHES[fname]
    opts = more[0] if more else {}
    condn, endn, matchn = opts.get('cond', 'hc'), opts.get('end', 'hc'), opts.get('match', 'hm')
    # With `reads`, the last entry is read and tested before the end is:
    # `end` takes the entry's facts but `cond`, and the entry doesn't match.
    reads = opts.get('reads', False)
    L = Loop(mf, mn)
    H = Stage(hf, hn_)
    E = Stage(ef, en)
    st, head, loopv = L.st, L.head, L.loopv
    hm = dict(H.params)[matchn]
    assert any(p == condn for p, _ in L.kept_per), f"no `{condn}` in the miss stage"
    cnt = L.primed(dict(E.params)[endn])
    valid = [(p, t) for p, t in L.kept_per if p != matchn]
    vcond = [(p, t) for p, t in valid if reads and p == condn]
    vrest = [(p, t) for p, t in valid if (p, t) not in vcond]
    N1 = "N + 1" if reads else "N"
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
    O(f"    (hz : ∀ {' '.join(ps)}, {L.peq('N')} → {cnt}) →")
    for p, t in head:
        O(f"    ({p} : {t}) →")
    vtext = " ∧ ".join(f"({L.primed(t)})" for _, t in vrest) or "True"
    O(f"    (∀ i, i < {N1} → ∀ {' '.join(ps)}, {L.peq('i')} → {vtext}) →")
    if reads:
        O(f"    (∀ i, i < N → ∀ {' '.join(ps)}, {L.peq('i')} → {L.primed(vcond[0][1])}) →")
    O(f"    SvErrRet B out v n0 ∨ ∃ k, k < {N1} ∧")
    O(f"      (∀ i, i < k → ∀ {' '.join(ps)}, {L.peq('i')} → ¬ ({L.primed(hm)})) ∧")
    O(f"      ∃ {' '.join(ps)}, {L.peq('k')} ∧ ({L.primed(hm)}) ∧")
    O("      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧")
    O(f"      SvKeepL B n0.mem nk.mem {L.kl} ∧")
    O(f"      {okname} {' '.join(fixed_names)} M0 {' '.join(ps)} nk := by")
    O("  intro N")
    O("  induction N with")
    O("  | zero =>")
    hc_ = " Hc" if reads else ""
    hit_ok = (f"(svIter_zero _ {tup}).symm, hm, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), okh⟩")
    if reads:
        O(f"    intro {' '.join(loopv)} n0 hz {' '.join(hn)} H _")
        O(f"    {bind(vrest)} := H 0 (Nat.succ_pos 0) {' '.join(loopv)} "
          f"(svIter_zero _ {tup}).symm")
        O(f"    by_cases hm : {subst(hm, L.local)}")
        hargs0 = ["hm" if p == matchn else "rfl" if (p, t) in L.per and (p, t) not in L.kept_per else p
                  for p, t in H.params]
        O(f"    · rcases {hn_} {L.named()} {' '.join(hargs0)} with {H.errpat} | okh")
        O("      · exact .inl e")
        O(f"      · exact .inr ⟨0, Nat.succ_pos 0, fun i hi => absurd hi (Nat.not_lt_zero i), {', '.join(loopv)}, "
          + hit_ok)
    else:
        O(f"    intro {' '.join(loopv)} n0 hz {' '.join(hn)} _")
    eargs = []
    for p, t in E.params:
        if p == endn:
            eargs.append(f"(hz {' '.join(loopv)} (svIter_zero _ {tup}).symm)")
        elif reads and p == matchn:
            eargs.append("hm")
        else:
            eargs.append("rfl" if (p, t) in L.per and (p, t) not in L.kept_per else p)
    ch = Chain(lambda x: None)
    _, enames, _, _ = ch.call(E, {p: a for (p, _), a in zip(E.params, eargs)})
    used = " ".join(t for _, t in E.params)
    edef = " ".join(f"({b} := {DEFAULTS[ty]})" for b, ty in E.binders
                    if b in L.local and not re.search(IDENT.format(re.escape(b)), used))
    O(f"    rcases {en} {L.named()} {edef} {' '.join(eargs)} with {E.errpat} | ⟨{', '.join(enames)}, -⟩")
    O("    · exact .inl e")
    O(f"    · exact {enames[0]}.elim")
    O("  | succ N ih =>")
    O(f"    intro {' '.join(loopv)} n0 hz {' '.join(hn)} H{hc_}")
    if reads:
        O(f"    {bind(vrest)} := H 0 (Nat.succ_pos _) {' '.join(loopv)} "
          f"(svIter_zero _ {tup}).symm")
        O(f"    have {condn} := Hc 0 (Nat.succ_pos N) {' '.join(loopv)} (svIter_zero _ {tup}).symm")
    elif valid:
        O(f"    obtain ⟨{', '.join(p for p, _ in valid)}⟩ := H 0 (Nat.succ_pos N) {' '.join(loopv)} "
          f"(svIter_zero _ {tup}).symm")
    else:
        O("    have _ := H")
    O(f"    by_cases hm : {subst(hm, L.local)}")
    hargs = []
    for p, t in H.params:
        hargs.append("hm" if p == matchn else "rfl" if (p, t) in L.per and (p, t) not in L.kept_per else p)
    O(f"    · rcases {hn_} {L.named()} {' '.join(hargs)} with {H.errpat} | okh")
    O("      · exact .inl e")
    O(f"      · exact .inr ⟨0, Nat.succ_pos _, fun i hi => absurd hi (Nat.not_lt_zero i), {', '.join(loopv)}, "
      + hit_ok)
    args = L.args({matchn: 'hm'})
    ch = Chain(lambda x: None)
    _, names1, pats1, _ = ch.call(st, {p: a for (p, _), a in zip(st.params, args)})
    O(f"    rcases {mn} {L.named()} {' '.join(args)} with {st.errpat} | ⟨{', '.join(names1 + pats1)}⟩")
    O("    · exact .inl e")
    ov = {'FW': 'FW', 'hret': 'hret', 'hO': 'hO', 'M0': 'M0', 'E0': 'E1', 'V0': 'V1', 's0': 's1', 'fM': 'fR1'}
    for p, _ in L.per:
        ov[p] = p
    a2, _, _, _ = ch.call(st, ov)
    a2 = a2[len(a2) - len(st.params):]
    hargs2 = [a for (p, _), a in zip(st.params, a2) if p in hn]
    vs = " ".join(ps)
    O(f"    rcases ih (fun {vs} e0 => hz {vs} (e0.trans (svIter_succ _ N {tup}).symm)) {' '.join(hargs2)}"
      f" (fun i hi {vs} e0 => H (i + 1) (Nat.succ_lt_succ hi) {vs} (e0.trans (svIter_succ _ i {tup}).symm))"
      + (f" (fun i hi {vs} e0 => Hc (i + 1) (Nat.succ_lt_succ hi) {vs} (e0.trans (svIter_succ _ i {tup}).symm))"
         if reads else "") +
      f" with e | ⟨k, hk, hn, {', '.join(ps)}, e0, hmk, nk, cs, h3, h4, hkl, okh⟩")
    O("    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)")
    O(f"    · refine .inr ⟨k + 1, by omega, fun i hi {vs} e1 => ?_, {', '.join(ps)}, "
      f"(e0.trans (svIter_succ _ k {tup}).symm), hmk, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, "
      "(K1_L.trans hkl).mono (by decide), okh⟩")
    O("      cases i with")
    O(f"      | zero => cases e1.trans (svIter_zero _ {tup}); exact hm")
    O(f"      | succ i => exact hn i (by omega) {vs} (e1.trans (svIter_succ _ i {tup}))")
    O("")
    stage_form(O, name, okname, L, H, ps, vrest, vcond, hm, cnt)
    if fname in RUNS:
        O("")
        run_form(O, name, L, ps, vrest, vcond, hm, cnt, *RUNS[fname])
    O("")
    O("end C3.RV32.Sv")
    O("")
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))


def stage_form(O, name, okname, L, H, ps, valid, vcond, hm, cnt):
    """The search as a stage: its hypotheses, then an error return or the
    entry that matches and the state at the end of `hit`."""
    fixed = " ".join(L.fixed)
    hn = [p for p, _ in L.head]
    nm = sc_pattern(H)
    facts = []
    for f in H.facts:
        if f.key == 'STEPS':
            continue
        t = L.primed(f.text)
        if f.key in ('r3', 'r4'):
            t = f"reg n' ({f.key[1]} : Fin 32) = reg n0 ({f.key[1]} : Fin 32)"
        elif f.key == 'KL':
            u = list(dict.fromkeys(re.findall(r"\(0x[0-9A-F]+, 0x[0-9A-F]+\)", L.kl + f.text)))
            t = "SvKeepL B n0.mem n'.mem [" + ", ".join(u) + "]"
        facts.append((f.key, f"({t})" if t.startswith('∀') else t))
    vtext = " ∧ ".join(f"({L.primed(t)})" for _, t in valid) or "True"
    N1 = "N + 1" if vcond else "N"
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O(f"/-- `{name}` as a stage. -/")
    O(f"theorem {name}_st {fixed} {{N : Nat}} {{{' '.join(L.loopv)} : Word}} {{n0 : Machine}}")
    O("    " + " ".join(f"({p} : {t})" for p, t in L.st.params if p in GLOBAL))
    O(f"    (hz : ∀ {' '.join(ps)}, {L.peq('N')} → {cnt})")
    for p, t in L.head:
        O(f"    ({p} : {t})")
    O(f"    (H : ∀ i, i < {N1} → ∀ {' '.join(ps)}, {L.peq('i')} → {vtext})" + ("" if vcond else " :"))
    if vcond:
        O(f"    (Hc : ∀ i, i < N → ∀ {' '.join(ps)}, {L.peq('i')} → {L.primed(vcond[0][1])}) :")
    O("    SvErrRet B out v n0 ∨")
    O(f"    (∃ k, k < {N1} ∧")
    O(f"      (∀ i, i < k → ∀ {' '.join(ps)}, {L.peq('i')} → ¬ ({L.primed(hm)})) ∧")
    O(f"      ∃ {' '.join(ps)}, {L.peq('k')} ∧ ({L.primed(hm)}) ∧")
    if H.sc_parts:
        O("      " + " ∧ ".join(L.primed(x) for x in H.sc_parts) + " ∧")
    O("    ∃ n', Steps n0 n' ∧")
    O("        " + " ∧\n        ".join(t for _, t in facts) + ") := by")
    lines = O.__self__
    i0 = max(i for i, l in enumerate(lines) if l.startswith("    SvErrRet B out v n0 ∨"))
    nb = RUNS_BOUND.get(name, 'N')
    open(f"/tmp/{name}_st.stmt", "w").write("\n".join(lines[i0:]).replace(L.peq('N'), L.peq(nb))
                                            .replace(f"∃ k, k < {N1} ∧", f"∃ k, k < {nb}{N1[1:]} ∧"))
    fixed_names = list(dict.fromkeys(b for g in L.fixed for b in g[1:g.rindex(' : ')].split()))
    O(f"  rcases {name} {' '.join(f'({b} := {b})' for b in fixed_names)} FW hret hO M0 N hz {' '.join(hn)} H{' Hc' if vcond else ''} with e | "
      f"⟨k, hk, hn, {', '.join(ps)}, e0, hmk, nk, cs, hr3, hr4, hkl, okh⟩")
    O("  · exact .inl e")
    O(f"  unfold {okname} at okh")
    O(f"  obtain ⟨{', '.join(nm + ['n1', 'cn'] + [f'f_{k}' for k, _ in facts])}⟩ := okh")
    terms = []
    for k, _ in facts:
        terms.append({"r3": "f_r3.trans hr3", "r4": "f_r4.trans hr4", "KL": "(hkl.trans f_KL).mono (by decide)"}.get(k, f"f_{k}"))
    O(f"  exact .inr ⟨k, hk, hn, {', '.join(ps)}, e0, hmk, {', '.join(nm + ['n1', 'cs.trans cn'] + terms)}⟩")



def run_form(O, name, L, ps, valid, vcond, hm, endt, cnt, base, bound):
    """`name_st` over every byte of the slice (`base`, `bound`) but its last:
    `cnt` counts up from 0, and each iteration reads the byte at `base + cnt`.
    It also gives the count at the entry that matches."""
    src = open(f"/tmp/{name}_st.stmt").read()
    assert L.loopv == [cnt], L.loopv
    F = f"({L.step})"
    zero = "BitVec.ofNat 32 0x0"
    z = lambda t: re.sub(IDENT.format(re.escape(cnt)), f"({zero})", t)
    hn = [p for p, _ in L.head]
    fixed_names = list(dict.fromkeys(b for g in L.fixed for b in g[1:g.rindex(' : ')].split()))
    pc = L.prime[cnt]
    closed = f"{pc} = ({zero}) + BitVec.ofNat 32 (k * 1) ∧"
    nb = RUNS_BOUND[name]
    O("set_option maxHeartbeats 16000000 in")
    O(f"/-- `{name}_st` over every byte of the slice but its last: `{cnt}` counts up from 0. -/")
    O(f"theorem {name}_run {' '.join(L.fixed)} {{n0 : Machine}}")
    O("    " + " ".join(f"({p} : {t})" for p, t in L.st.params if p in GLOBAL))
    for p, t in L.head:
        O(f"    ({p} : {z(t)})")
    O(f"    (slice : SvIn B {base} {bound}.toNat) (hlen : {bound} ≠ 0) :")
    for line in src.split("\n"):
        O(z(line))
        if line.strip().startswith(f"∃ {' '.join(ps)}, ") and line.strip().endswith("∧"):
            O("      " + closed)
    inc = f"svIter_add (F := {F}) (fun s : Word => s) (d := 1) (fun s => rfl)"
    vtext = " ∧ ".join(f"({z(L.primed(t))})" for _, t in valid) or "True"
    ctext = z(L.primed(vcond[0][1]))
    O(f"  have hb := slice.fit")
    O(f"  have hl : {bound}.toNat ≠ 0 := fun h => hlen (BitVec.eq_of_toNat_eq (by rw [h]; rfl))")
    O(f"  have HZ : ∀ {' '.join(ps)}, {z(L.peq(nb))} → {z(endt)} := by")
    O(f"    intro {' '.join(ps)} e")
    O(f"    rw [e, {inc}]")
    O("    bv_omega")
    O(f"  have HH : ∀ i, i < {nb} + 1 → ∀ {' '.join(ps)}, {z(L.peq('i'))} → {vtext} := by")
    O(f"    intro i hi {' '.join(ps)} e")
    O(f"    rw [e, {inc}, BitVec.zero_add, Nat.mul_one]")
    O("    exact (slice.drop (k := i) (by omega)).shrink (by omega)")
    O(f"  have HC : ∀ i, i < {nb} → ∀ {' '.join(ps)}, {z(L.peq('i'))} → {ctext} := by")
    O(f"    intro i hi {' '.join(ps)} e")
    O(f"    rw [e, {inc}, BitVec.zero_add, Nat.mul_one]")
    O("    bv_omega")
    O(f"  rcases {name}_st {' '.join(f'({b} := {b})' for b in fixed_names)} ({cnt} := {zero}) (N := {nb}) "
      f"FW hret hO M0 HZ {' '.join(hn)} HH HC with e | ⟨k, hk, hn, {', '.join(ps)}, e0, hmk, rest⟩")
    O("  · exact .inl e")
    O(f"  have h1 : {pc} = ({zero}) + BitVec.ofNat 32 (k * 1) := by rw [e0, {inc}]")
    O(f"  exact .inr ⟨k, hk, hn, {', '.join(ps)}, e0, hmk, h1, rest⟩")


if __name__ == "__main__":
    for f in sys.argv[1:] or SEARCHES:
        write(f)
