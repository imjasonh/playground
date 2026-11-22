"""Writes a merged stage of `sigstore::verify`: two generated stages that
start at the same place under a hypothesis and its negation, and reach the
same place with the same facts.

The merged theorem takes the first stage's hypotheses except that one. It
ends in an error return, or in either stage's success condition followed
by their common facts. Its proof splits on the hypothesis and passes each
stage's facts on whole, so it never takes them apart.
"""

import re

from svchain import DEFAULTS, Stage, lean_binders, strip_parens, top_split
from svseg import Segment, canon, split_in, strip_exists


class SliceCtx(Segment):
    """The slices a stage's hypotheses and success condition give, for `Segment.derive_in`."""

    def __init__(self, stage, names):
        self.ins, self.parses, self.bits, self.eqs, self.nl, self.contents, self.les = [], {}, {}, {}, {}, {}, {}
        self.closed, self.lts = {}, {}
        for p, t in stage.params:
            if t.startswith('SvIn B '):
                ptr, n = split_in(t[len('SvIn B '):])
                self.ins.append((ptr, n, p))
        proofs = [x for x in names if re.fullmatch(r"h\d+", x)]
        pieces = [strip_exists(x.strip()) for part in stage.sc_parts for x in top_split(part, ' ∧ ')]
        self.pairs = list(zip(proofs, pieces))
        self.record(self.pairs)


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


def complement(x, y):
    """How hypothesis type `y` follows from `¬ x`: a term from `¬ x` named `h`,
    and whether `y` needs a witness first. None if it doesn't."""
    if negates(x, y):
        return ("{h}", None)
    m = re.fullmatch(r"(.+) < (.+)", x)
    if m and y == f"{m.group(2)} ≤ {m.group(1)}":
        return ("(Nat.not_lt.mp {h})", None)
    m = re.fullmatch(r"(.+) = none", x)
    m2 = m and re.fullmatch(re.escape(m.group(1)) + r" = some (\w+)", y)
    if m2:
        return ("{h}w", "obtain ⟨{h}v, {h}w⟩ := Option.ne_none_iff_exists'.mp {h}", m2.group(1), m.group(1))
    return None


def split(stages, names):
    """A decision tree over `stages`: a hypothesis that some of them take, and
    one that follows from its negation that the others take, then the trees
    of each side."""
    if len(stages) == 1:
        return ('leaf', stages[0])
    for p, t in [pt for st in stages for pt in st.params]:
        pos = [st for st in stages if dict(st.params).get(p) == t]
        rest = [st for st in stages if st not in pos]
        if not rest:
            continue
        negmap, pre, wit = {}, None, None
        for st in rest:
            found = None
            for q, u in st.params:
                c = complement(t, u)
                if c:
                    found = (q, c)
                    break
            if not found:
                break
            negmap.setdefault(st.name, {})[found[0]] = found[1][0]
            pre = pre or found[1][1]
            wit = found[1][2:] if len(found[1]) > 2 else None
        else:
            # The negated side must take the complement in every stage, by the same name.
            qs = {tuple(m) for m in (tuple(sorted(v)) for v in negmap.values())}
            if len(qs) != 1:
                continue
            h = "hb" if not names else f"hb{len(names) + 1}"
            names.append(p)
            neg = {q: f.format(h=h) for q, f in next(iter(negmap.values())).items()}
            names += [q for q in neg if q != p]
            return ('split', p, t, h, split(pos, names), split(rest, names), neg,
                    pre.format(h=h) if pre else None, (wit[0], wit[1], h) if pre and wit else None)
    raise ValueError(f"no hypothesis tells {[st.name for st in stages]} apart")


def subst_w(text, subs):
    for b, e in subs.items():
        text = re.sub(rf"(?<![\w.']){re.escape(b)}(?![\w'])", e, text)
    return text


def leaves(tree):
    return [tree[1]] if tree[0] == 'leaf' else leaves(tree[4]) + leaves(tree[5])


def witnesses_of(tree, acc=(), out=None):
    """For each leaf, the witnesses that decisions above it introduce: (binder, expression, hypothesis)."""
    out = {} if out is None else out
    if tree[0] == 'leaf':
        out[tree[1].name] = list(acc)
        return out
    witnesses_of(tree[4], acc, out)
    witnesses_of(tree[5], acc + ((tree[8],) if tree[8] else ()), out)
    return out


def merged(fname, name, vs, doc):
    """Writes a merged stage from the stages `vs`, a list of (file, theorem)."""
    files = {Stage(*v).name: v[0] for v in vs}
    conds = []
    tree = split([Stage(*v) for v in vs], conds)
    order = leaves(tree)
    wits = witnesses_of(tree)
    bound = {b for ws in wits.values() for b, _, _ in ws}
    a = order[0]
    types = {'w': 'Word', 'r': 'Word', 'b': 'BitVec 8', 'a': 'Nat'}
    # A stage whose success condition is `False` only ever fails; it states nothing at its end.
    vac = {st.name for st in order if st.sc_parts and strip_parens(st.sc_parts[0]) == 'False'}
    live = [st for st in order if st.name not in vac] or order
    a = live[0]
    common = [f.key for f in a.facts if all(f.key in {g.key for g in st.facts} for st in live)]
    # A fact the stages state differently that can't be a witness's value is left out.
    reorder = None
    fa, dvars = [], []
    kl_union = None
    # Facts that differ only by a list in place of a list binder: the list becomes a witness.
    ltexts = {st.name: {k: next(f.text for f in st.facts if f.key == k) for k in common} for st in live}
    lsub = None
    for ref in live:
        for b, ty in ref.binders:
            if ty != 'Bytes':
                continue
            vals, ok = {}, True
            for k in common:
                t0 = ltexts[ref.name][k]
                if all(ltexts[st.name][k] == t0 for st in live) or not re.search(rf"(?<![\w.']){re.escape(b)}(?![\w'])", t0):
                    continue
                pat = re.escape(t0)
                pat = re.sub(rf"(?<![\w.']){re.escape(re.escape(b))}(?![\w'])", lambda _: "(.+?)", pat)
                for st in live:
                    mm = re.fullmatch(pat, ltexts[st.name][k])
                    if not mm or len(set(mm.groups())) != 1:
                        ok = False
                        break
                    v = mm.group(1)
                    if vals.setdefault(st.name, v) != v:
                        ok = False
                        break
                if not ok:
                    break
            if ok and vals and len(set(vals.values())) > 1:
                lsub = (b, ref.name, vals)
                break
        if lsub:
            break
    if lsub:
        b, rname, vals = lsub
        d = f"{name.removeprefix('sv_')}_{b}"
        dvars.append((d, 'Bytes', [vals.get(st.name, b) for st in order]))
        for st in live:
            for k in common:
                t = ltexts[rname][k]
                if re.search(rf"(?<![\w.']){re.escape(b)}(?![\w'])", t):
                    new_t = re.sub(rf"(?<![\w.']){re.escape(b)}(?![\w'])", d, t)
                    for f in st.facts:
                        if f.key == k:
                            f.text = new_t
    common = [k for k in common if k == 'KL' or k[0] in types or
              len({next(g.text for g in st.facts if g.key == k) for st in live}) == 1]
    reorder = [[f.key for f in st.facts] != common for st in order]
    for fs in zip(*[[next(f for f in st.facts if f.key == k) for k in common] for st in live]):
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
            by_live = {st.name: f.rhs for st, f in zip(live, fs)}
            dvars.append((d, types[x.key[0]], [by_live.get(st.name, fs[0].rhs) for st in order]))
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
    bgroups = [g for g in ("{" + " ".join(x for x in g[1:g.rindex(' : ')].split() if x not in bound) + g[g.rindex(' : '):]
                           for g in bgroups) if not g.startswith("{ :")]
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
    scs = ["False" if st.name in vac else
           " ∧ ".join([f"∃ {b}, {x} = some {b}" for b, x, _ in wits[st.name]] + st.sc_parts +
                      [f"{d} = {vals[j]}" for d, _, vals in dvars]) or "True"
           for j, st in enumerate(order)]
    dbind = "".join(f"∃ {d} : {t}, " for d, t, _ in dvars)
    slices = []
    dk = {d: i for i, (d, _, _) in enumerate(dvars)}
    for d, _, _ in dvars:
        stem = name.removeprefix('sv_')
        m = re.fullmatch(rf"{stem}_w([0-9a-f]+)", d)
        for dl in ([f"{stem}_w{int(m.group(1), 16) + o:x}" for o in (4, -4)] if m else []):
            if dl not in dk:
                continue
            terms = []
            for j, st in enumerate(order):
                ctx = SliceCtx(st, sc_pattern(st))
                terms.append("-" if st.name in vac else
                             ctx.derive_in(canon(dvars[dk[d]][2][j]), canon(f"({dvars[dk[dl]][2][j]}).toNat")))
            if all(terms):
                slices.append((d, dl, terms))
                break
    slice_text = "".join(f" ∧ SvIn B {d} {dl}.toNat" for d, dl, _ in slices)
    # A pointer that some branches keep and others set to a slice they parse:
    # it is 0 or a slice, given that the kept one is.
    cslices = []
    sliced = {x for d, dl, _ in slices for x in (d, dl)}
    for d, ty_d, vals in dvars:
        if ty_d != 'Word' or d in sliced:
            continue
        stem = name.removeprefix('sv_')
        m = re.fullmatch(rf"{stem}_w([0-9a-f]+)", d)
        dl = f"{stem}_w{int(m.group(1), 16) + 4:x}" if m else None
        dl = dl if dl in dk and dl not in sliced else None
        base, terms, lens, ok = None, [], set(), True
        for j, st in enumerate(order):
            if st.name in vac:
                terms.append("-")
                continue
            v = canon(vals[j])
            vl = canon(dvars[dk[dl]][2][j]) if dl else None
            ob = {b for b, _ in st.binders}
            if v in ob and (dl is None or vl in ob):
                if base not in (None, (v, vl)):
                    ok = False
                    break
                base = (v, vl)
                terms.append(None)
                continue
            ctx = SliceCtx(st, sc_pattern(st))
            if dl:
                S, L = ctx.derive_in(v, canon(f"({vl}).toNat")), f"{dl}.toNat"
            else:
                S, L = ctx.derive_lit(v)
            if not S:
                ok = False
                break
            lens.add(L)
            terms.append(f".inr ({S})")
        if not ok or base is None or len(lens) != 1 or all(t in (None, "-") for t in terms):
            continue
        L = lens.pop()
        X, XL = base
        hn = f"{X}_or0"
        hyps.append((hn, f"{X} = 0 ∨ SvIn B {X} {XL + '.toNat' if dl else L}"))
        cslices.append((d, L, [hn if t is None else t for t in terms]))
    slice_text += "".join(f" ∧ ({d} = 0 ∨ SvIn B {d} {L})" for d, L, _ in cslices)
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

    def named_for(st):
        named = named_of[st.name]
        for wb, _, wh in wits[st.name]:
            named = named.replace(f"({wb} := {wb})", f"({wb} := {wh}v)")
        for wb in bound - {x for x, _, _ in wits[st.name]}:
            ty = dict(st.binders).get(wb)
            if ty:
                named = named.replace(f"({wb} := {wb})", f"({wb} := {DEFAULTS[ty]})")
        return named

    def leaf(st, path, ind, bare=False):
        j = order.index(st)
        wsub = {wb: f"{wh}v" for wb, _, wh in wits[st.name]}
        if st.name in vac:
            named = named_for(st)
            args = " ".join(path.get(p, p) for p, _ in st.params)
            b = "" if bare else "· "
            sub = ind if bare else ind + "  "
            out.append(f"{ind}{b}rcases {st.name} {named} {args} with {st.errpat} | ⟨hf, -⟩")
            out.append(f"{sub}· exact .inl e")
            out.append(f"{sub}· exact hf.elim")
            return
        nm = sc_pattern(st)
        pat = f"⟨{', '.join(nm)}, rest⟩" if nm else "rest"
        prs = [y for _, _, h in wits[st.name] for y in (f"{h}v", f"{h}w")] + nm + ["rfl"] * len(dvars)
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
        vals = "".join(f"{subst_w(v[j], wsub)}, " for _, _, v in dvars)
        args = " ".join(path.get(p, p) for p, _ in st.params)
        sl = "".join(f"{ts[j]}, " for _, _, ts in slices + cslices)
        b = "" if bare else "· "
        sub = ind if bare else ind + "  "
        named = named_for(st)
        out.append(f"{ind}{b}rcases {st.name} {named} {args} with {st.errpat} | {pat}")
        out.append(f"{sub}· exact .inl e")
        if pre:
            out.append(f"{sub}· {pre.strip()}")
            out.append(f"{sub}  exact .inr ⟨{vals}{side(pf, j)}, {sl}{rest}⟩")
        else:
            out.append(f"{sub}· exact .inr ⟨{vals}{side(pf, j)}, {sl}{rest}⟩")

    def emit(t, path, ind, top=False, bare=False, subs=None):
        subs = subs or {}
        if t[0] == 'leaf':
            leaf(t[1], path, ind, bare)
            return
        if bare:
            _, p, ty, h, pos, neg, negmap, pre, wit = t
            ty = subst_w(ty, subs)
            nsubs = {**subs, wit[0]: f"{wit[2]}v"} if wit else subs
            out.append(f"{ind}by_cases {h} : {ty}")
            emit(pos, {**path, p: h}, ind, subs=subs)
            if pre:
                out.append(f"{ind}· {pre}")
                emit(neg, {**path, **negmap}, ind + "  ", bare=True, subs=nsubs)
            else:
                emit(neg, {**path, **negmap}, ind, subs=nsubs)
            return
        _, p, ty, h, pos, neg, negmap, pre, wit = t
        ty = subst_w(ty, subs)
        nsubs = {**subs, wit[0]: f"{wit[2]}v"} if wit else subs
        if top:
            out.append(f"{ind}by_cases {h} : {ty}")
            inner = ind
        else:
            out.append(f"{ind}· by_cases {h} : {ty}")
            inner = ind + "  "
        emit(pos, {**path, p: h}, inner, subs=subs)
        if pre:
            out.append(f"{inner}· {pre}")
            emit(neg, {**path, **negmap}, inner + "  ", top=False, bare=True, subs=nsubs)
        else:
            emit(neg, {**path, **negmap}, inner, subs=nsubs)

    emit(tree, {}, "  ", top=True)
    out += ["", "end C3.RV32.Sv", ""]
    open(f'C3BootProofs/Proofs/{fname}.lean', 'w').write("\n".join(out))
