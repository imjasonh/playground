"""Writes a merged stage of `sigstore::verify`: two generated stages that
start at the same place under a hypothesis and its negation, and reach the
same place with the same facts.

The merged theorem takes the first stage's hypotheses except that one. It
ends in an error return, or in either stage's success condition followed
by their common facts. Its proof splits on the hypothesis and passes each
stage's facts on whole, so it never takes them apart.
"""

import re

from svchain import Stage, groups


def negates(x, y):
    return y in (f"¬ {x}", f"¬ ({x})") or (' = ' in x and y == x.replace(' = ', ' ≠ ', 1))


def sc_pattern(stage):
    """Names that take a stage's success condition apart, and the term that rebuilds it."""
    names = []
    n = 0
    from svchain import top_split
    for part in stage.sc_parts:
        for piece in top_split(part, ' ∧ '):
            piece = piece.strip()
            while piece.startswith('∃ '):
                c = piece.index(',')
                names += [f"w{n}_{b}" for b in piece[2:c].split()]
                piece = piece[c + 1:].strip()
            names.append(f"h{n}")
            n += 1
    return names


def merged(fname, name, va, vb, doc):
    a, b = Stage(*va), Stage(*vb)
    ta, tb = dict(a.params), dict(b.params)
    cond = None
    for p in ta:
        if p in tb and ta[p] != tb[p]:
            if negates(ta[p], tb[p]):
                cond = p
            elif negates(tb[p], ta[p]):
                cond = p
                a, b, va, vb = b, a, vb, va
                ta, tb = tb, ta
    assert cond, (a.name, b.name)
    assert all(ta[p] == tb[p] for p in ta if p != cond and p in tb), "the stages' hypotheses disagree"
    fa = [f.text for f in a.facts]
    assert fa == [f.text for f in b.facts], "the stages leave different facts"
    assert a.binders == b.binders
    src = open(f'C3BootProofs/Proofs/{va[0]}.lean').read()
    i = src.index(f'theorem {a.name} ')
    binders = src[i + len(f'theorem {a.name} '):src.index('(F : ', i)].strip()
    hyps = [(p, t) for p, t in a.params if p != cond] + [(p, t) for p, t in b.params if p not in ta]
    sca = " ∧ ".join(a.sc_parts) if a.sc_parts else "True"
    scb = " ∧ ".join(b.sc_parts) if b.sc_parts else "True"
    facts = fa[1:]
    named = " ".join(f"({x} := {x})" for x, _ in a.binders)
    args = {st.name: " ".join(p if p != cond else "hb" for p, _ in st.params) for st in (a, b)}
    out = [f"import C3BootProofs.Proofs.{va[0]}", f"import C3BootProofs.Proofs.{vb[0]}", "",
           f"/-!\n# `sigstore::verify`: {doc}\n\nWritten by `scripts/gen-sv-segs.py` from `{a.name}` and `{b.name}`.\n-/",
           "", "namespace C3.RV32.Sv", ""]
    for line in src.split('\n'):
        if line.startswith('open '):
            out += [line, ""]
            break
    out.append("set_option maxHeartbeats 16000000 in")
    out.append(f"/-- {doc} -/")
    out.append(f"theorem {name} {binders}")
    out += [f"    ({p} : {t})" for p, t in hyps]
    out[-1] += " :"
    out.append("    SvErrRet B out v n0 ∨")
    out.append(f"    ((({sca}) ∨ ({scb})) ∧")
    out.append("    ∃ n', Steps n0 n' ∧")
    out += [f"        {t}" + (" ∧" if j + 1 < len(facts) else ")") for j, t in enumerate(facts)]
    out[-1] += " := by"
    out.append(f"  by_cases hb : {ta[cond]}")
    for side, st in ((".inl", a), (".inr", b)):
        nm = sc_pattern(st)
        pat = f"⟨{', '.join(nm)}, rest⟩" if nm else "rest"
        pf = ("⟨" + ", ".join(nm) + "⟩" if len(nm) > 1 else nm[0]) if nm else "trivial"
        out.append(f"  · rcases {st.name} {named} {args[st.name]} with ⟨-, e⟩ | {pat}")
        out.append("    · exact .inl e")
        out.append(f"    · exact .inr ⟨{side} {pf}, rest⟩")
    out += ["", "end C3.RV32.Sv", ""]
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))
