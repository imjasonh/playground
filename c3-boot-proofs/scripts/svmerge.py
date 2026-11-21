"""Writes a merged stage of `sigstore::verify`: two generated stages that
start at the same place under a hypothesis and its negation, and reach the
same place with the same facts.

The merged theorem takes the first stage's hypotheses except that one. It
ends in an error return, or in either stage's success condition followed
by their common facts. Its proof splits on the hypothesis and passes each
stage's facts on whole, so it never takes them apart.
"""

import re

from svchain import Stage, top_split
from svseg import Segment, canon, split_in, strip_exists


class SliceCtx(Segment):
    """The slices a stage's hypotheses and success condition give, for `Segment.derive_in`."""

    def __init__(self, stage, names):
        self.ins, self.parses, self.bits, self.eqs, self.nl = [], {}, {}, {}, {}
        for p, t in stage.params:
            if t.startswith('SvIn B '):
                ptr, n = split_in(t[len('SvIn B '):])
                self.ins.append((ptr, n, p))
        proofs = [x for x in names if re.fullmatch(r"h\d+", x)]
        pieces = [strip_exists(x.strip()) for part in stage.sc_parts for x in top_split(part, ' ∧ ')]
        self.record(list(zip(proofs, pieces)))


def negates(x, y):
    return y in (f"¬ {x}", f"¬ ({x})") or (' = ' in x and y == x.replace(' = ', ' ≠ ', 1))


def sc_pattern(stage):
    """Names that take a stage's success condition apart, and the term that rebuilds it."""
    names = []
    n = 0
    for part in stage.sc_parts:
        for piece in top_split(part, ' ∧ '):
            piece = piece.strip()
            while piece.startswith('∃ '):
                c = piece.index(',')
                names += piece[2:c].split(":")[0].split()
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
    assert [f.key for f in a.facts] == [f.key for f in b.facts], "the stages leave different facts"
    types = {'w': 'Word', 'r': 'Word', 'b': 'BitVec 8', 'a': 'Nat'}
    fa, dvars = [], []
    kl_union = None
    for x, y in zip(a.facts, b.facts):
        if x.text == y.text:
            fa.append(x.text)
        elif x.key == 'KL':
            la = re.findall(r"\(0x[0-9A-F]+, 0x[0-9A-F]+\)", x.text)
            lb = re.findall(r"\(0x[0-9A-F]+, 0x[0-9A-F]+\)", y.text)
            kl_union = la + [r for r in lb if r not in la]
            fa.append("SvKeepL B n0.mem n'.mem [" + ", ".join(kl_union) + "]")
        else:
            d = f"d_{x.key}"
            dvars.append((d, types[x.key[0]], x.rhs, y.rhs))
            fa.append(x.text[:len(x.text) - len(x.rhs)] + d)
    assert a.binders == b.binders
    src = open(f'C3BootProofs/Proofs/{va[0]}.lean').read()
    i = src.index(f'theorem {a.name} ')
    binders = src[i + len(f'theorem {a.name} '):src.index('(F : ', i)].strip()
    hyps = [(p, t) for p, t in a.params if p != cond] + [(p, t) for p, t in b.params if p not in ta]
    sca = " ∧ ".join(a.sc_parts + [f"{d} = {va}" for d, _, va, _ in dvars]) or "True"
    scb = " ∧ ".join(b.sc_parts + [f"{d} = {vb}" for d, _, _, vb in dvars]) or "True"
    dbind = "".join(f"∃ {d} : {t}, " for d, t, _, _ in dvars)
    slices = []
    dk = {d: i for i, (d, _, _, _) in enumerate(dvars)}
    for d, _, _, _ in dvars:
        m = re.fullmatch(r"d_w([0-9a-f]+)", d)
        dl = f"d_w{int(m.group(1), 16) + 4:x}" if m else None
        if dl in dk:
            terms = []
            for i, st in enumerate((a, b)):
                ctx = SliceCtx(st, sc_pattern(st))
                ptr = canon(dvars[dk[d]][2 + i])
                n = canon(f"({dvars[dk[dl]][2 + i]}).toNat")
                terms.append(ctx.derive_in(ptr, n))
            if all(terms):
                slices.append((d, dl, terms))
    slice_text = "".join(f" ∧ SvIn B {d} {dl}.toNat" for d, dl, _ in slices)
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
    out.append(f"    ({dbind}(({sca}) ∨ ({scb})){slice_text} ∧")
    out.append("    ∃ n', Steps n0 n' ∧")
    out += [f"        {t}" + (" ∧" if j + 1 < len(facts) else ")") for j, t in enumerate(facts)]
    out[-1] += " := by"
    out.append(f"  by_cases hb : {ta[cond]}")
    nfacts = len(facts)
    for i, (side, st) in enumerate(((".inl", a), (".inr", b))):
        nm = sc_pattern(st)
        pat = f"⟨{', '.join(nm)}, rest⟩" if nm else "rest"
        prs = nm + ["rfl"] * len(dvars)
        pf = ("⟨" + ", ".join(prs) + "⟩" if len(prs) > 1 else prs[0]) if prs else "trivial"
        if kl_union is not None:
            chain = "fun k => k.mono (by decide)"
            for _ in range(nfacts):
                chain = f"fun h => h.imp_right ({chain})"
            rest = f"rest.imp (fun _ => {chain})"
        else:
            rest = "rest"
        vals = "".join(f"{(va, vb)[i]}, " for _, _, va, vb in dvars)
        out.append(f"  · rcases {st.name} {named} {args[st.name]} with ⟨-, e⟩ | {pat}")
        out.append("    · exact .inl e")
        sl = "".join(f"{ts[i]}, " for _, _, ts in slices)
        out.append(f"    · exact .inr ⟨{vals}{side} {pf}, {sl}{rest}⟩")
    out += ["", "end C3.RV32.Sv", ""]
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))
