"""Writes a merged stage of `sigstore::verify`: two generated stages that
start at the same place under a hypothesis and its negation, and reach the
same place with the same facts.

The merged theorem takes the first stage's hypotheses except that one. It
ends in an error return, or in either stage's success condition followed
by their common facts. Its proof splits on the hypothesis and passes each
stage's facts on whole, so it never takes them apart.
"""

import re

from svchain import Stage, lean_binders, top_split
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


def split(stages, names):
    """A decision tree over `stages`: a hypothesis that some of them take and
    the others take negated, then the trees of each side."""
    if len(stages) == 1:
        return ('leaf', stages[0])
    first = dict(stages[0].params)
    for p, t in stages[0].params:
        tys = [dict(st.params).get(p) for st in stages]
        if None in tys or len(set(tys)) != 2:
            continue
        pos_t = next((x for x in set(tys) if any(negates(x, y) for y in set(tys))), None)
        if pos_t is None:
            continue
        pos = [st for st, ty in zip(stages, tys) if ty == pos_t]
        neg = [st for st, ty in zip(stages, tys) if ty != pos_t]
        h = "hb" if not names else f"hb{len(names) + 1}"
        names.append(p)
        return ('split', p, pos_t, h, split(pos, names), split(neg, names))
    raise ValueError(f"no hypothesis tells {[st.name for st in stages]} apart")


def leaves(tree):
    return [tree[1]] if tree[0] == 'leaf' else leaves(tree[4]) + leaves(tree[5])


def merged(fname, name, vs, doc):
    """Writes a merged stage from the stages `vs`, a list of (file, theorem)."""
    files = {Stage(*v).name: v[0] for v in vs}
    conds = []
    tree = split([Stage(*v) for v in vs], conds)
    order = leaves(tree)
    a = order[0]
    common = [f.key for f in a.facts if all(f.key in {g.key for g in st.facts} for st in order)]
    reorder = [[f.key for f in st.facts] != common for st in order]
    types = {'w': 'Word', 'r': 'Word', 'b': 'BitVec 8', 'a': 'Nat'}
    fa, dvars = [], []
    kl_union = None
    for fs in zip(*[[next(f for f in st.facts if f.key == k) for k in common] for st in order]):
        x = fs[0]
        if all(f.text == x.text for f in fs):
            fa.append(x.text)
        elif x.key == 'KL':
            kl_union = []
            for f in fs:
                kl_union += [r for r in re.findall(r"\(0x[0-9A-F]+, 0x[0-9A-F]+\)", f.text) if r not in kl_union]
            fa.append("SvKeepL B n0.mem n'.mem [" + ", ".join(kl_union) + "]")
        else:
            d = f"{name.removeprefix('sv_')}_{x.key}"
            dvars.append((d, types[x.key[0]], [f.rhs for f in fs]))
            fa.append(x.text[:len(x.text) - len(x.rhs)] + d)
    src = open(f'C3BootProofs/Proofs/{files[a.name]}.lean').read()
    own = {st.name: lean_binders(files[st.name], st.name) for st in order}
    seen_b, bgroups = set(), []
    for st in order:
        for names, ty in own[st.name]:
            new_names = [x for x in names if x not in seen_b]
            seen_b |= set(new_names)
            if new_names:
                bgroups.append("{" + " ".join(new_names) + " : " + ty + "}")
    binders = " ".join(bgroups)
    hyps, seen = [], set()
    for st in order:
        for p, t in st.params:
            if p in conds or p in seen:
                continue
            seen.add(p)
            hyps.append((p, t))
    for st in order:
        assert all(dict(hyps)[p] == t for p, t in st.params if p not in conds), "the stages' hypotheses disagree"
    scs = [" ∧ ".join(st.sc_parts + [f"{d} = {vals[j]}" for d, _, vals in dvars]) or "True"
           for j, st in enumerate(order)]
    dbind = "".join(f"∃ {d} : {t}, " for d, t, _ in dvars)
    slices = []
    dk = {d: i for i, (d, _, _) in enumerate(dvars)}
    for d, _, _ in dvars:
        stem = name.removeprefix('sv_')
        m = re.fullmatch(rf"{stem}_w([0-9a-f]+)", d)
        dl = f"{stem}_w{int(m.group(1), 16) + 4:x}" if m else None
        if dl in dk:
            terms = []
            for j, st in enumerate(order):
                ctx = SliceCtx(st, sc_pattern(st))
                terms.append(ctx.derive_in(canon(dvars[dk[d]][2][j]), canon(f"({dvars[dk[dl]][2][j]}).toNat")))
            if all(terms):
                slices.append((d, dl, terms))
    slice_text = "".join(f" ∧ SvIn B {d} {dl}.toNat" for d, dl, _ in slices)
    facts = fa[1:]
    named_of = {st.name: " ".join(f"({x} := {x})" for names, _ in own[st.name] for x in names) for st in order}
    who = ", ".join(f"`{st.name}`" for st in order[:-1]) + (" and " if len(order) == 2 else ", and ") + f"`{order[-1].name}`"
    out = [f"import C3BootProofs.Proofs.{files[st.name]}" for st in order] + [
           "", f"/-!\n# `sigstore::verify`: {doc}\n\nWritten by `scripts/gen-sv-segs.py` from {who}.\n-/",
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
    out.append(f"    ({dbind}(" + " ∨ ".join(f"({x})" for x in scs) + f"){slice_text} ∧")
    out.append("    ∃ n', Steps n0 n' ∧")
    out += [f"        {t}" + (" ∧" if j + 1 < len(facts) else ")") for j, t in enumerate(facts)]
    out[-1] += " := by"
    nfacts = len(facts)
    n = len(order)

    def side(pf, j):
        t = f".inl {pf}" if j < n - 1 else pf
        for _ in range(j):
            t = f".inr {t}" if t.startswith('⟨') or ' ' not in t else f".inr ({t})"
        return t

    def leaf(st, path, ind):
        j = order.index(st)
        nm = sc_pattern(st)
        pat = f"⟨{', '.join(nm)}, rest⟩" if nm else "rest"
        prs = nm + ["rfl"] * len(dvars)
        pf = ("⟨" + ", ".join(prs) + "⟩" if len(prs) > 1 else prs[0]) if prs else "trivial"
        if reorder[j]:
            own = [f.key for f in st.facts if f.key != 'STEPS']
            out_names = {k: f"f_{k}" for k in own}
            pre = f"{ind}    obtain ⟨n', fc, {', '.join(out_names[k] for k in own)}⟩ := rest\n"
            terms = [out_names[k] + (".mono (by decide)" if k == 'KL' else "") for k in common if k != 'STEPS']
            rest = f"⟨n', fc, {', '.join(terms)}⟩"
        elif kl_union is not None:
            pre = ""
            chain = "fun k => k.mono (by decide)"
            for _ in range(nfacts):
                chain = f"fun h => h.imp_right ({chain})"
            rest = f"rest.imp (fun _ => {chain})"
        else:
            pre = ""
            rest = "rest"
        vals = "".join(f"{v[j]}, " for _, _, v in dvars)
        args = " ".join(path.get(p, p) for p, _ in st.params)
        sl = "".join(f"{ts[j]}, " for _, _, ts in slices)
        out.append(f"{ind}· rcases {st.name} {named_of[st.name]} {args} with {st.errpat} | {pat}")
        out.append(f"{ind}  · exact .inl e")
        if pre:
            out.append(f"{ind}  · {pre.strip()}")
            out.append(f"{ind}    exact .inr ⟨{vals}{side(pf, j)}, {sl}{rest}⟩")
        else:
            out.append(f"{ind}  · exact .inr ⟨{vals}{side(pf, j)}, {sl}{rest}⟩")

    def emit(t, path, ind, top=False):
        if t[0] == 'leaf':
            leaf(t[1], path, ind)
            return
        _, p, ty, h, pos, neg = t
        if top:
            out.append(f"{ind}by_cases {h} : {ty}")
            inner = ind
        else:
            out.append(f"{ind}· by_cases {h} : {ty}")
            inner = ind + "  "
        emit(pos, {**path, p: h}, inner)
        emit(neg, {**path, p: h}, inner)

    emit(tree, {}, "  ", top=True)
    out += ["", "end C3.RV32.Sv", ""]
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))
