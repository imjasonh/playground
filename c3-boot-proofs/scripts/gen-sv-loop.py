#!/usr/bin/env python3
"""Writes the loop theorems of `sigstore::verify` whose body is one generated
stage that returns to the loop's head.

The stage's hypotheses about the machine (registers, frame words, code,
saves, and the frame outside the stack) are the loop's invariant. The
binders that the stage's facts change are the loop's variables, each
updated by a function of itself alone; after `k` iterations each is that
function iterated `k` times, so `svIter f (k + 1) x` unfolds to
`svIter f k (f x)` and
the induction step passes the rest of the run on whole. The stage's other
hypotheses hold for each iteration's values. Binders that only those name,
each set by one of them to a read of memory, are replaced by that read.

Usage: python3 scripts/gen-sv-loop.py [name ...]   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import IDENT, Chain, Stage, subst  # noqa: E402
from svloop import GLOBAL, Loop  # noqa: E402
from svmerge import sc_pattern  # noqa: E402

# Loops that a stage leaves once a variable is 0: file: (exit file, exit theorem, variable).
EXITS = {'SvCkdLoop': ('SvCke', 'sv_cke', 'c')}
# Loops over a slice, one byte an iteration: file: (pointer, the slice's hypothesis).
RUNS = {'SvCkdLoop': ('p', 'pin')}

# file: (theorem, body stage, doc)
LOOPS = {
    'SvILoop': ('sv_iloop', ('SvImiss', 'sv_imiss'),
                "the search of the root's Fulcio intermediates for the leaf's issuer, over `k` entries that "
                "don't match"),
    'SvTLoop': ('sv_tloop', ('SvTlmiss', 'sv_tlmiss'),
                "the search of the root's TSAs for the timestamp's signer, over `k` entries that don't match"),
    'SvCLoop': ('sv_cloop', ('SvClmiss', 'sv_clmiss'),
                "the search of the root's logs for the checkpoint's origin, over `k` entries that don't match"),
    'SvCkdLoop': ('sv_ckdloop', ('SvCkd', 'sv_ckd'), "the checkpoint's size, over `k` digits"),
}



def paren(t):
    return f"({t})" if t.startswith('∀') else t


def write(fname):
    name, (sfile, sname), doc = LOOPS[fname]
    L = Loop(sfile, sname)
    st, head, loopv = L.st, L.head, L.loopv
    hn = [p for p, _ in head]
    Doc = doc[0].upper() + doc[1:]
    out = []
    O = out.append
    O("import C3BootProofs.Proofs.SvSeg")
    O(f"import C3BootProofs.Proofs.{sfile}")
    if fname in EXITS:
        O(f"import C3BootProofs.Proofs.{EXITS[fname][0]}")
    O("")
    O(f"/-!\n# `sigstore::verify`: {Doc}\n\nWritten by `scripts/gen-sv-loop.py` from `{sname}`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    O(L.opens())
    O("")
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O(f"/-- {Doc}. -/")
    O(f"theorem {name} {' '.join(L.fixed)}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL) + " :")
    O(f"    ∀ (k : Nat) {{{' '.join(loopv)} : Word}} {{n0 : Machine}},")
    for p, t in head:
        O(f"    ({p} : {t}) →")
    if L.kept_per:
        O(f"    (∀ i, i < k → ∀ {' '.join(L.prime.values())}, {L.peq('i')} → " +
          " ∧ ".join(f"({L.primed(t)})" for _, t in L.kept_per) + ") →")
    O(f"    SvErrRet B out v n0 ∨ ∃ n' {' '.join(L.prime.values())}, Steps n0 n' ∧ {L.peq('k')} ∧")
    O("      reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧")
    O(f"      SvKeepL B n0.mem n'.mem {L.kl} ∧")
    O("      " + " ∧\n      ".join(paren(L.primed(t, "n'")) for _, t in head) + " := by")
    tup = L.tup()
    O("  intro k")
    O("  induction k with")
    O("  | zero =>")
    O(f"    intro {' '.join(loopv)} n0 {' '.join(hn)}" + (" _" if L.kept_per else ""))
    O(f"    exact .inr ⟨n0, {', '.join(loopv)}, .refl _, (svIter_zero _ {tup}).symm, rfl, rfl, SvKeepL.refl.mono "
      f"(by decide), {', '.join(hn)}⟩")
    O("  | succ k ih =>")
    O(f"    intro {' '.join(loopv)} n0 {' '.join(hn)}" + (" H" if L.kept_per else ""))
    if L.kept_per:
        O(f"    obtain ⟨{', '.join(p for p, _ in L.kept_per)}⟩ := H 0 (Nat.succ_pos k) {' '.join(loopv)} "
          f"(svIter_zero _ {tup}).symm")
    args = L.args()
    ch = Chain(lambda x: None)
    _, names1, pats1, _ = ch.call(st, {p: a for (p, _), a in zip(st.params, args)})
    O(f"    rcases {sname} {L.named()} {' '.join(args)} with ⟨-, e⟩ | ⟨{', '.join(names1 + pats1)}⟩")
    O("    · exact .inl e")
    ov = {'F': 'F', 'hret': 'hret', 'hO': 'hO', 'M0': 'M0', 'E0': 'E1', 'V0': 'V1', 's0': 's1', 'fM': 'fR1'}
    for p, _ in L.per:
        ov[p] = p
    a2, _, _, _ = ch.call(st, ov)
    a2 = a2[len(a2) - len(st.params):]
    hargs = [a for (p, _), a in zip(st.params, a2) if p in hn]
    vs = " ".join(L.prime.values())
    O(f"    rcases ih {' '.join(hargs)}" +
      (f" (fun i hi {vs} e0 => H (i + 1) (Nat.succ_lt_succ hi) {vs} (e0.trans (svIter_succ _ i {tup}).symm))"
       if L.kept_per else "") +
      f" with e | ⟨n', {', '.join(L.prime.values())}, cs, e0, h3, h4, hk, rest⟩")
    O("    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)")
    O(f"    · exact .inr ⟨n', {', '.join(L.prime.values())}, c1.trans cs, (e0.trans (svIter_succ _ k {tup}).symm), "
      "h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), rest⟩")
    if fname in EXITS:
        O("")
        exit_form(O, name, L, *EXITS[fname])
    if fname in RUNS:
        O("")
        run_form(O, name, L, *EXITS[fname], *RUNS[fname])
    O("")
    O("end C3.RV32.Sv")
    O("")
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))


def exit_form(O, name, L, efile, ename, cnt):
    """`N` iterations of the loop, then the stage `ename` that leaves it once
    `cnt` is 0, as one stage."""
    E = Stage(efile, ename)
    st, head = L.st, L.head
    ps = list(L.prime.values())
    pr = dict(zip(L.loopv, ps))
    hn = [p for p, _ in head]
    extra = [(p, t) for p, t in E.params if p not in {q for q, _ in st.params}]
    facts = []
    for f in E.facts:
        if f.key == 'STEPS':
            continue
        t = subst(f.text, pr)
        if f.key in ('r3', 'r4'):
            t = f"reg n' ({f.key[1]} : Fin 32) = reg n0 ({f.key[1]} : Fin 32)"
        elif f.key == 'KL':
            u = list(dict.fromkeys(re.findall(r"\(0x[0-9A-F]+, 0x[0-9A-F]+\)", L.kl + f.text)))
            t = "SvKeepL B n0.mem n'.mem [" + ", ".join(u) + "]"
        facts.append((f.key, f"({t})" if t.startswith('∀') else t))
    enm = sc_pattern(E)
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O(f"/-- `N` iterations of `{name}`, then `{ename}`, as a stage. -/")
    O(f"theorem {name}_st {' '.join(L.fixed)} {{N : Nat}} {{{' '.join(L.loopv)} : Word}} {{n0 : Machine}}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL))
    O(f"    (hz : ∀ {' '.join(ps)}, {L.peq('N')} → {cnt}' = 0)")
    for p, t in head:
        O(f"    ({p} : {t})")
    O(f"    (H : ∀ i, i < N → ∀ {' '.join(ps)}, {L.peq('i')} → " +
      " ∧ ".join(f"({L.primed(t)})" for _, t in L.kept_per) + ")")
    for p, t in extra:
        if p != 'hc':
            O(f"    ({p} : {subst(subst(t, L.local), pr)})")
    O("    :")
    concl = ["    SvErrRet B out v n0 ∨", f"    (∃ {' '.join(ps)}, {L.peq('N')} ∧"]
    if E.sc_parts:
        concl.append("      " + " ∧ ".join(subst(x, pr) for x in E.sc_parts) + " ∧")
    concl.append("    ∃ n', Steps n0 n' ∧")
    concl.append("        " + " ∧\n        ".join(t for _, t in facts) + ") := by")
    for line in concl:
        O(line)
    for p, t in extra:
        if p != 'hc':
            concl.insert(0, f"    ({p} : {subst(subst(t, L.local), pr)})")
    concl.insert(len([x for x in extra if x[0] != 'hc']), "    :")
    open(f'/tmp/{name}_st.stmt', 'w').write("\n".join(c.replace("svIter (", "svIter (", 1) for c in concl)
                                            .replace(L.peq('N'), L.peq(f"{cnt}.toNat")))
    h1 = [f"{p}'" for p in hn]
    O(f"  rcases {name} F hret hO M0 N {' '.join(hn)} H with e | ⟨n1, {', '.join(ps)}, cs, e0, hr3, hr4, hkl, "
      f"{', '.join(h1)}⟩")
    O("  · exact .inl e")
    rn = dict(zip(hn, h1))
    rn.update({'hc': f"(hz {' '.join(ps)} e0)"})
    eargs = " ".join(rn.get(p, p) for p, _ in E.params)
    enamed = " ".join(f"({b} := {pr.get(b, b)})" for names, _ in L.binders for b in names if b in E.binder_set()
                      and b not in L.local and b != 'n0')
    O(f"  rcases {ename} {enamed} {eargs} with ⟨-, e⟩ | ⟨{', '.join(enm + ['n2', 'c2'] + [f'f_{k}' for k, _ in facts])}⟩")
    O(f"  · exact .inl (SvErrRet.pre cs hr3 hr4 (fun x hx => ({rn['fM']} x hx).trans (fM x hx).symm) e)")
    terms = [{"r3": "f_r3.trans hr3", "r4": "f_r4.trans hr4", "KL": "(hkl.trans f_KL).mono (by decide)"}.get(k, f"f_{k}")
             for k, _ in facts]
    O(f"  exact .inr ⟨{', '.join(ps)}, e0, {', '.join(enm + ['n2', 'cs.trans c2'] + terms)}⟩")



def run_form(O, name, L, efile, ename, cnt, ptr, slice_hyp):
    """The loop and its exit over every byte of the slice (`ptr`, `cnt`): the
    count reaches 0 after `cnt.toNat` iterations, and each iteration has its
    byte."""
    E = Stage(efile, ename)
    st, head = L.st, L.head
    ps = list(L.prime.values())
    hn = [p for p, _ in head]
    extra = [p for p, _ in E.params if p not in {q for q, _ in st.params}]
    j_cnt, j_ptr = L.loopv.index(cnt), L.loopv.index(ptr)
    n = len(L.loopv)

    def proj(j):
        return "s" + ".2" * j + (".1" if j + 1 < n else "")
    src = open(f'C3BootProofs/Proofs/{L.sfile}.lean').read()
    O("set_option maxHeartbeats 16000000 in")
    O(f"/-- `{name}_st` over every byte of the slice: `{cnt}` reaches 0 after `{cnt}.toNat` iterations. -/")
    stmt = [l for l in open(f'/tmp/{name}_st.stmt').read().split('\n')]
    O(f"theorem {name}_run {' '.join(L.fixed)} {{{' '.join(L.loopv)} : Word}} {{n0 : Machine}}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL))
    for p, t in head:
        O(f"    ({p} : {t})")
    O(f"    ({slice_hyp} : {dict(L.kept_per)[slice_hyp]})")
    for line in stmt:
        O(line)
    F = f"({L.step})"
    T = " × ".join(["Word"] * n)
    O(f"  refine {name}_st (N := {cnt}.toNat) F hret hO M0 ?_ {' '.join(hn)} ?_ {' '.join(x for x in extra if x != 'hc')}")
    dec = f"svIter_dec1 (F := {F}) (fun s : {T} => {proj(j_cnt)}) (fun s => rfl)"
    inc = f"svIter_add (F := {F}) (fun s : {T} => {proj(j_ptr)}) (d := 1) (fun s => rfl)"
    O(f"  · intro {' '.join(ps)} e")
    O(f"    have h1 := congrArg (fun s => {proj(j_cnt)}) e")
    O("    simp only at h1")
    O(f"    rw [{dec}] at h1")
    O("    simp only at h1")
    O(f"    rw [h1]; exact svSub_self_toNat {cnt}")
    O(f"  · intro i hi {' '.join(ps)} e")
    O(f"    have h1 := congrArg (fun s => {proj(j_cnt)}) e")
    O(f"    have h2 := congrArg (fun s => {proj(j_ptr)}) e")
    O("    simp only at h1 h2")
    O(f"    rw [{dec}] at h1")
    O(f"    rw [{inc}] at h2")
    O("    simp only at h1 h2")
    O("    refine ⟨?_, ?_⟩")
    O("    · rw [h1]; bv_omega")
    O(f"    · rw [h1, h2, Nat.mul_one, svSub_toNat (by omega)]; exact {slice_hyp}.drop (by omega)")


if __name__ == "__main__":
    for f in sys.argv[1:] or LOOPS:
        write(f)
