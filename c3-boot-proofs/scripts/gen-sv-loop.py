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
from svchain import IDENT, Chain, Stage, groups, param_key, strip_parens, subst, top_split  # noqa: E402

# file: (theorem, body stage, doc)
LOOPS = {
    'SvILoop': ('sv_iloop', ('SvImiss', 'sv_imiss'),
                "the search of the root's Fulcio intermediates for the leaf's issuer, over `k` entries that "
                "don't match"),
}

GLOBAL = ('F', 'hret', 'hO', 'M0')
Z = "(svIter_zero _ _).symm"
S = "(svIter_succ _ _ _).symm"
HEAD_EXTRA = ('E0', 'V0', 's0', 'fM')


def paren(t):
    return f"({t})" if t.startswith('∀') else t


def write(fname):
    name, (sfile, sname), doc = LOOPS[fname]
    st = Stage(sfile, sname)
    src = open(f'C3BootProofs/Proofs/{sfile}.lean').read()
    i = src.index(f'theorem {sname} ')
    header = src[i + len(f'theorem {sname} '):src.index('(F : ', i)].strip()
    binders = []
    for g in groups(header, '{', '}'):
        names, ty = g.rsplit(' : ', 1)
        binders.append((names.split(), ty))
    bset = {b for names, _ in binders for b in names}
    head = [(p, t) for p, t in st.params if p in HEAD_EXTRA or param_key(p)]
    per = [(p, t) for p, t in st.params if p not in GLOBAL and (p, t) not in head]
    facts = {f.key: f for f in st.facts}
    upd = {}
    for p, t in head:
        key = param_key(p)
        if not key:
            continue
        rhs = strip_parens(top_split(t, ' = ')[-1])
        f = facts.get(key) or facts.get('ra' + key[2:] if re.fullmatch(r'r1[0-7]', key) else '')
        if f is None:
            raise ValueError(f"{sname} doesn't keep {p}")
        new = strip_parens(f.rhs)
        if new != rhs:
            if rhs not in bset or rhs in upd:
                raise ValueError(f"{p}: {rhs} -> {new}")
            upd[rhs] = new
    for b, e in upd.items():
        others = {x for x in bset if x != b and re.search(IDENT.format(re.escape(x)), e)} & set(upd)
        if others:
            raise ValueError(f"{b}'s update {e} names other loop variables {others}")
    head_text = " ".join(t for _, t in head)
    local = {}
    kept_per = []
    for p, t in per:
        parts = top_split(t, ' = ')
        rhs = strip_parens(parts[-1]) if len(parts) == 2 else None
        if rhs in bset and rhs not in upd and rhs not in local and not re.search(IDENT.format(re.escape(rhs)), head_text):
            local[rhs] = strip_parens(parts[0])
        else:
            kept_per.append((p, t))
    loopv = list(upd)

    def it(b, K):
        e = re.sub(IDENT.format(re.escape(b)), 'x', upd[b])
        return f"(svIter (fun x => {e}) {K} {b})"

    def at(t, K, mach="n0"):
        t = subst(t, local)
        t = subst(t, {b: it(b, K) for b in loopv})
        return re.sub(IDENT.format("n0"), mach, t)

    fixed = []
    for names, ty in binders:
        keep = [b for b in names if b not in upd and b not in local and b != 'n0']
        if keep:
            fixed.append("{" + " ".join(keep) + " : " + ty + "}")
    lv = "{" + " ".join(loopv) + " : Word}"
    out = []
    O = out.append
    O(f"import C3BootProofs.Proofs.SvSeg")
    O(f"import C3BootProofs.Proofs.{sfile}")
    O("")
    O(f"/-!\n# `sigstore::verify`: {doc[0].upper() + doc[1:]}\n\nWritten by `scripts/gen-sv-loop.py` from `{sname}`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    for line in src.split('\n'):
        if line.startswith('open '):
            O(line)
            O("")
            break
    O("set_option maxHeartbeats 16000000 in")
    O("set_option maxRecDepth 100000 in")
    O(f"/-- {doc[0].upper() + doc[1:]}. -/")
    O(f"theorem {name} {' '.join(fixed)}")
    O("    " + " ".join(f"({p} : {t})" for p, t in st.params if p in GLOBAL) + " :")
    O(f"    ∀ (k : Nat) {lv} {{n0 : Machine}},")
    for p, t in head:
        O(f"    ({p} : {at(t, 0) if False else t}) →")
    prime = {b: b + "'" for b in loopv}
    eqs = lambda K: " ∧ ".join(f"{b}' = {it(b, K)}" for b in loopv)
    if kept_per:
        O(f"    (∀ i, i < k → ∀ {' '.join(prime.values())}, " + " → ".join(f"{b}' = {it(b, 'i')}" for b in loopv) +
          " → " + " ∧ ".join(f"({subst(subst(t, local), prime)})" for _, t in kept_per) + ") →")
    kl = re.search(r"\[.*\]", facts['KL'].text).group(0)
    O(f"    SvErrRet B out v n0 ∨ ∃ n' {' '.join(prime.values())}, Steps n0 n' ∧ {eqs('k')} ∧")
    O("      reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧")
    O(f"      SvKeepL B n0.mem n'.mem {kl} ∧")
    O("      " + " ∧\n      ".join(paren(re.sub(IDENT.format("n0"), "n'", subst(subst(t, local), prime)))
                                   for _, t in head) + " := by")
    hn = [p for p, _ in head]
    O("  intro k")
    O("  induction k with")
    O("  | zero =>")
    O(f"    intro {' '.join(loopv)} n0 {' '.join(hn)}" + (" _" if kept_per else ""))
    O(f"    exact .inr ⟨n0, {', '.join(loopv)}, .refl _, {(Z + ', ') * len(loopv)}rfl, rfl, SvKeepL.refl.mono (by decide), "
      f"{', '.join(hn)}⟩")
    O("  | succ k ih =>")
    O(f"    intro {' '.join(loopv)} n0 {' '.join(hn)}" + (" H" if kept_per else ""))
    if kept_per:
        O(f"    obtain ⟨{', '.join(p for p, _ in kept_per)}⟩ := H 0 (Nat.succ_pos k) {' '.join(loopv)} {(Z + ' ') * len(loopv)}".rstrip())
    args = []
    for p, t in st.params:
        if p in local.values() or (p, t) in per and (p, t) not in kept_per:
            args.append("rfl")
        else:
            args.append(p)
    named = " ".join(f"({b} := {b})" for names, _ in binders for b in names if b not in local and b != 'n0')
    ch = Chain(lambda x: None)
    a1, names1, pats1, _ = ch.call(st, {p: a for (p, _), a in zip(st.params, args)})
    O(f"    rcases {sname} {named} {' '.join(args)} with ⟨-, e⟩ | ⟨{', '.join(names1 + pats1)}⟩")
    O("    · exact .inl e")
    ov = {'F': 'F', 'hret': 'hret', 'hO': 'hO', 'M0': 'M0', 'E0': 'E1', 'V0': 'V1', 's0': 's1', 'fM': 'fR1'}
    for p, t in per:
        ov[p] = p
    a2, _, _, _ = ch.call(st, ov)
    a2 = a2[len(a2) - len(st.params):]
    hargs = [a for (p, _), a in zip(st.params, a2) if p in hn]
    vs = " ".join(prime.values())
    es = " ".join(f"e{j}" for j in range(len(loopv)))
    sh = " ".join(f"(e{j}.trans {S})" for j in range(len(loopv)))
    O(f"    rcases ih {' '.join(hargs)}" +
      (f" (fun i hi {vs} {es} => H (i + 1) (Nat.succ_lt_succ hi) {vs} {sh})" if kept_per else "") +
      f" with e | ⟨n', {', '.join(prime.values())}, cs, {', '.join(f'e{j}' for j in range(len(loopv)))}, h3, h4, hk, rest⟩")
    O("    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)")
    O(f"    · exact .inr ⟨n', {', '.join(prime.values())}, c1.trans cs, {sh.replace(') (', '), (')}, "
      "h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), rest⟩")
    O("")
    O("end C3.RV32.Sv")
    O("")
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))


if __name__ == "__main__":
    for f in sys.argv[1:] or LOOPS:
        write(f)
