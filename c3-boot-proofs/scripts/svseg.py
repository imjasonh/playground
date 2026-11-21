"""Writes a segment theorem of `sigstore::verify`: a run of generated stages,
composed with `svchain.Chain`.

The theorem takes the first stage's hypotheses. It ends in an error
return, a panic, or every stage's success condition followed by the state
at the segment's end. The success conditions stay one chain of conjuncts,
so later conditions and facts can name earlier stages' witnesses.

A later stage's hypothesis that no earlier fact gives is one of:
- a hypothesis of the first stage with the same name and type;
- a code or data fact about `M0`, which the theorem also takes;
- an `SvIn` fact about a slice that a DER parse in an earlier success
  condition found, which `SvIn.contentW`, `SvIn.restW`, and `SvIn.rawW`
  derive from the slice it parsed;
- a term from `extra`.
"""

import copy
import re

from svchain import Chain, Fact, Stage, fname, param_key, strip_parens, subst, top_split

GLOBAL_TYPES = ('CodeIn M0', 'P2Data M0', 'P2Code M0', 'BYEnv M0', 'BGEnv M0', 'SvEcCode M0', 'SvIvCode M0',
                'SvUpCode M0', 'SvRoSep B', 'SvShaCode M0', 'PvEnv7 M0', 'SvWnCode M0', 'SvKSep B')


def strip_exists(part):
    while part.startswith('∃ '):
        part = part[part.index(',') + 1:].strip()
    return part


def witnesses(stage, k):
    ren = {}
    for part in stage.sc_parts:
        for piece in top_split(part, ' ∧ '):
            piece = piece.strip()
            while piece.startswith('∃ '):
                c = piece.index(',')
                for b in piece[2:c].split(":")[0].split():
                    ren[b] = f"{b}_{k}"
                piece = piece[c + 1:].strip()
    return ren


def split_in(s):
    """The pointer and length word of `SvIn B p l.toNat`'s arguments `p l.toNat`."""
    parts = [x for x in top_split(s.strip(), ' ') if x]
    return canon(parts[0]), canon(" ".join(parts[1:]))


def split_sum(e):
    """The top-level terms of a `+`/`-` chain: [(op, term)], the first op ''."""
    out, depth, cur, op, i = [], 0, '', '', 0
    while i < len(e):
        c = e[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        if depth == 0 and (e.startswith(' + ', i) or e.startswith(' - ', i)):
            out.append((op, cur))
            op, cur = e[i + 1], ''
            i += 3
            continue
        cur += c
        i += 1
    out.append((op, cur))
    return out


def canon(e):
    """`e` without parentheses that left association or application makes redundant."""
    e = strip_parens(e.strip())
    terms = split_sum(e)
    if len(terms) > 1:
        out = canon(terms[0][1])
        for op, t in terms[1:]:
            c = canon(t)
            out += f" {op} " + (f"({c})" if len(split_sum(c)) > 1 else c)
        return out
    toks = [t for t in top_split(e, ' ') if t]
    if len(toks) > 1:
        return " ".join(canon_atom(t) for t in toks)
    return canon_atom(e) if e.startswith('(') else e


def canon_atom(t):
    m = re.fullmatch(r"(\(.*\))((?:\.\w+)*)", t)
    if m and strip_parens(m.group(1)) != m.group(1):
        c = canon(m.group(1))
        atomic = len([x for x in top_split(c, ' ') if x]) == 1
        return (c if atomic else f"({c})") + m.group(2)
    return t


def chain_steps(K):
    s = f"c{K}"
    for k in range(K - 1, 0, -1):
        s = f"c{k}.trans ({s})"
    return s


def part_count(part):
    """How many names `Chain` gives a success condition's part: one for each
    witness and one for each conjunct's proof."""
    n = 0
    for piece in top_split(part, ' ∧ '):
        piece = piece.strip()
        while piece.startswith('∃ '):
            c = piece.index(',')
            n += len(piece[2:c].split(":")[0].split())
            piece = piece[c + 1:].strip()
        n += 1
    return n


def counter(step, init):
    """A search's counter, the first part of its state: its start and what
    each step adds, when both are constants."""
    st = re.fullmatch(r"\(\(s\.1\)\) \+ BitVec\.ofNat 32 (0x[0-9A-F]+), .+", step)
    c0 = strip_parens(init)
    if st and re.fullmatch(r"BitVec\.ofNat 32 0x[0-9A-F]+", c0):
        return c0, int(st.group(1), 16)
    return None


class Segment:
    def __init__(self, name, seq, doc, extra=None):
        self.name = name
        self.items = [('merge', [Stage(*y) for y in x[1]]) if x[0] == 'merge' else ('stage', Stage(*x)) for x in seq]
        self.stages = [it[1] for it in self.items if it[0] == 'stage']
        self.seq = seq
        self.doc = doc
        self.extra = extra or {}

    def derive_in(self, ptr, n):
        """A proof of `SvIn B ptr n`, with `ptr` and the length `n` in `canon` form."""
        for p, l, pf in self.ins:
            if p == ptr and l == n:
                return pf
        for ix, (hp, P0, N0) in self.nl.items():
            m = re.fullmatch(rf"{re.escape(P0)} \+ BitVec\.ofNat 32 (0x[0-9A-Fa-f]+|\d+)", ptr)
            if m and ix in self.les:
                k = int(m.group(1), 0)
                lpf, lk = self.les[ix]
                if lk == k and n == canon(f"(BitVec.ofNat 32 {ix} + BitVec.ofNat 32 0x{0x100000000 - k:X}).toNat"):
                    base = self.derive_in(P0, N0)
                    if base:
                        return f"SvIn.dropLit (k := {k}) (({base}).nlLine {hp}) {lpf} (by decide)"
            if ptr == P0 and n in (canon(ix), canon(f"(BitVec.ofNat 32 {ix}).toNat")):
                base = self.derive_in(P0, N0)
                if base:
                    t = f"({base}).nlLine {hp}"
                    return t if n == canon(ix) else f"({t}).ofNatLen"
            if ptr == canon(f"{P0} + BitVec.ofNat 32 ({ix} + 1)") and n == canon(f"{N0} - ({ix} + 1)"):
                base = self.derive_in(P0, N0)
                if base:
                    return f"({base}).nlRest {hp}"
        mc = re.fullmatch(r"([\w']+)\.toNat", n)
        if mc and mc.group(1) in self.closed:
            cpf, k = self.closed[mc.group(1)]
            if k in self.lts:
                kpf, Lw = self.lts[k]
                S = self.derive_in(ptr, canon(f"({Lw}).toNat"))
                if S:
                    return f"SvIn.beforeSep ({S}) {kpf} {cpf}"
        m = re.fullmatch(r"(.+) \+ \(([\w']+) \+ BitVec\.ofNat 32 0x1\)", ptr)
        if m and m.group(2) in self.closed:
            cpf, k = self.closed[m.group(2)]
            if k in self.lts:
                kpf, Lw = self.lts[k]
                cand = canon(f"((({Lw}) - ({m.group(2)} + BitVec.ofNat 32 0x1)) >>> 2).toNat * 4")
                cand_all = canon(f"(({Lw}) - ({m.group(2)} + BitVec.ofNat 32 0x1)).toNat")
                if n in (cand, cand_all):
                    S = self.derive_in(canon(m.group(1)), canon(f"({Lw}).toNat"))
                    if S:
                        lemma = "afterSep" if n == cand else "afterSepAll"
                        return f"SvIn.{lemma} ({S}) {kpf} {cpf}"
        if ptr in self.contents:
            hp, P0, N0, l, lemma = self.contents[ptr]
            if n == canon(f"{l}.toNat"):
                base = self.derive_in(P0, N0)
                if base:
                    return f"({base}).{lemma} {hp}"
        if ptr in self.bits:
            pf, tl, bl = self.bits[ptr]
            if tl in self.parses:
                hp, P0, N0 = self.parses[tl]
                base = self.derive_in(P0, N0)
                if base:
                    term = f"SvIn.bitsW ({base}) {hp} {pf}"
                    if n == canon(f"{bl}.toNat"):
                        return term
                    if bl in self.eqs and self.eqs[bl][1] == n:
                        return f"by have h := {term}; rw [{self.eqs[bl][0]}] at h; exact h"
        m = re.fullmatch(r"(.+) \+ BitVec\.ofNat 32 (\w+)\.header", ptr)
        if m and m.group(2) in self.parses:
            w = m.group(2)
            hp, P0, N0 = self.parses[w]
            if canon(m.group(1)) == P0:
                base = self.derive_in(P0, N0)
                if base and n == canon(f"{w}.len"):
                    return f"({base}).content {hp}"
                if base and n == canon(f"(BitVec.ofNat 32 {w}.len).toNat"):
                    return f"(({base}).content {hp}).ofNatLen"
        m = re.fullmatch(r"(.+) \+ BitVec\.ofNat 32 \((\w+)\.header \+ \2\.len\)", ptr)
        if m and m.group(2) in self.parses:
            w = m.group(2)
            hp, P0, N0 = self.parses[w]
            hl = f"BitVec.ofNat 32 ({w}.header + {w}.len)"
            if canon(m.group(1)) == P0:
                base = self.derive_in(P0, N0)
                if base and N0.endswith('.toNat') and n == canon(f"({N0[:-6]} - {hl}).toNat"):
                    return f"({base}).restW {hp}"
                if base and n == canon(f"{N0} - ({w}.header + {w}.len)"):
                    return f"({base}).rest {hp}"
                if base and n == canon(f"(BitVec.ofNat 32 ({N0}) - {hl}).toNat"):
                    return f"({base}).restN {hp}"
        for w, (hp, P0, N0) in self.parses.items():
            if P0 != ptr:
                continue
            base = None
            if n == canon(f"{w}.header + {w}.len") and N0.endswith('.toNat'):
                base = self.derive_in(P0, N0)
                if base:
                    return f"({base}).rawN {hp}"
            if n == canon(f"(BitVec.ofNat 32 ({w}.header + {w}.len)).toNat") and N0.endswith('.toNat'):
                base = self.derive_in(P0, N0)
                if base:
                    return f"({base}).rawW {hp}"
        return None

    def match_sc(self, ty, free):
        """An earlier success-condition conjunct that is `ty` with its unassigned
        binders `free` filled in: its proof and the binders' values."""
        free = sorted(free, key=len, reverse=True)
        pat = re.escape(canon(ty))
        for i, b in enumerate(free):
            pat = re.sub(rf"(?<![\w.']){re.escape(re.escape(b))}(?![\w'])", f"\x00{i}\x00", pat)
        for i, b in enumerate(free):
            pat = pat.replace(f"\x00{i}\x00", f"(?P<g{i}>[\\w.']+)", 1).replace(f"\x00{i}\x00", f"(?P=g{i})")
        hits = []
        for pf, piece in self.pieces:
            m = re.fullmatch(pat, canon(piece))
            if m:
                hits.append((pf, {b: m.group(f"g{i}") for i, b in enumerate(free) if f"g{i}" in m.groupdict()}))
        return hits[-1] if hits else None

    def record(self, proofs):
        """Remembers the slices that the parses in a success condition found."""
        self.pieces = getattr(self, 'pieces', []) + list(proofs)
        for pf, piece in proofs:
            piece = strip_parens(piece)
            m = re.fullmatch(r"derElement \S+ \(memBytes M0 (.+)\) = \.ok (\w+)", piece)
            if m:
                ptr, ln = split_in(m.group(1))
                self.parses[m.group(2)] = (pf, ptr, ln)
            toks = [x for x in top_split(piece, ' ') if x]
            if len(toks) == 7 and toks[0] == 'derBitsOf' and toks[4] == '=' and toks[5] == '.ok':
                tl = re.fullmatch(r"\(\.ok (\w+)\)", toks[3])
                pr = re.fullmatch(r"\((\w+), (\w+)\)", toks[6])
                if tl and pr:
                    self.bits[pr.group(1)] = (pf, tl.group(1), pr.group(2))
            m = re.fullmatch(r"(\w+) = BitVec\.ofNat 32 (\S+)", piece)
            if m:
                self.eqs[m.group(1)] = (pf, m.group(2))
            toks = [x for x in top_split(piece, ' ') if x]
            if len(toks) == 6 and toks[0] == 'derContent' and toks[3] == '=' and toks[4] == '.ok':
                inner = strip_parens(toks[2])
                pr = re.fullmatch(r"\((\w+), (\w+)\)", toks[5])
                m2 = re.fullmatch(r"(derOid|derElement \S+) \(memBytes M0 (.+)\)", inner)
                if pr and m2:
                    ptr, ln = split_in(m2.group(2))
                    lemma = "oidIn" if m2.group(1) == "derOid" else "contentIn"
                    self.contents[pr.group(1)] = (pf, ptr, ln, pr.group(2), lemma)
            if piece.startswith('SvIn B '):
                ptr, n = split_in(piece[len('SvIn B '):])
                self.ins.append((ptr, n, pf))
            m = re.fullmatch(r"(\d+|0x[0-9A-Fa-f]+) ≤ (\w+)", piece)
            if m:
                self.les[m.group(2)] = (pf, int(m.group(1), 0))
            m = re.fullmatch(r"\(?([\w']+)\)? = \(BitVec\.ofNat 32 0x0\) \+ BitVec\.ofNat 32 \((\w+) \* 1\)", piece)
            if m:
                self.closed[m.group(1)] = (pf, m.group(2))
            m = re.fullmatch(r"(\w+) < (.+)\.toNat", piece)
            if m:
                self.lts[m.group(1)] = (pf, canon(m.group(2)))
            m = re.fullmatch(r"nlScan M0 (\S+|\(.+\)) 0 (\S+|\(.+\)) = some (\w+)", piece)
            if m:
                self.nl[m.group(3)] = (pf, canon(m.group(1)), canon(m.group(2)))
            m = re.fullmatch(r"derOid \(memBytes M0 (.+)\) = \.ok (\w+)", piece)
            if m:
                ptr, ln = split_in(m.group(1))
                self.parses[m.group(2)] = (f"(derOid_ok_elem {pf})", ptr, ln)
            m = re.fullmatch(r"derOptRes \S+ \(memBytes M0 (.+)\) = some \(\.ok (\w+)\)", piece)
            if m:
                ptr, ln = split_in(m.group(1))
                self.parses[m.group(2)] = (f"(opt_ok_elem {pf})", ptr, ln)

    def fail(self, kk, kind, P, indent="  "):
        """The proof of the segment's goal from step `kk`'s error return or panic `e`."""
        if kind == 'Both':
            self.fail(kk, 'SvErrRet', P, indent)
            self.fail(kk, 'Panics', P, indent)
            return
        if kk == 1:
            P(f"{indent}· exact .inr (.inl e)" if kind == 'Panics' else f"{indent}· exact .inl e")
        elif kind == 'Panics':
            P(f"{indent}· exact .inr (.inl (Panics.of_steps ({chain_steps(kk - 1)}) e))")
        else:
            r3 = ", ".join(f"r{j}_3" for j in range(kk - 1, 0, -1))
            r4 = ", ".join(f"r{j}_4" for j in range(kk - 1, 0, -1))
            P(f"{indent}· exact .inl (SvErrRet.pre ({chain_steps(kk - 1)}) (by rw [{r3}]) (by rw [{r4}])")
            P(f"{indent}    (fun x hx => (fR{kk - 1} x hx).trans (fM x hx).symm) e)")

    def merge(self, ch, variants, ov, P):
        """Two stages from one place, by a hypothesis and its negation, that reach the same place."""
        a, b = variants
        ta, tb = dict(a.params), dict(b.params)
        neg = lambda x, y: y == f"¬ {x}" or y == f"¬ ({x})" or (' = ' in x and y == x.replace(' = ', ' ≠ ', 1))
        cond = None
        for p in ta:
            if p in tb and ta[p] != tb[p]:
                if neg(ta[p], tb[p]):
                    cond = p
                elif neg(tb[p], ta[p]):
                    cond = p
                    a, b = b, a
                    ta, tb = tb, ta
        if cond is None:
            raise ValueError(f"no condition tells {a.name} from {b.name}")
        k = ch.k
        kk = k + 1
        runs = []
        for st in (a, b):
            c2 = copy.copy(ch)
            o = dict(ov)
            o[cond] = 'hb'
            args, names, pats, sc = c2.call(st, o, resolve=self.resolve, wren=witnesses(st, kk))
            args = ([] if c2.at else []) + args
            tcond = subst(re.sub(r"(?<![\w.'])n0(?![\w'])", f"n{k}", dict(st.params)[cond]), c2.env)
            runs.append((st, ('@' if c2.at else '') + st.name + ' ' + " ".join(args), names, pats, sc, c2.prev, tcond))
        fa, fb = runs[0][5], runs[1][5]
        if list(fa) != list(fb):
            raise ValueError(f"{a.name} and {b.name} leave different facts")
        types = {'w': 'Word', 'r': 'Word', 'b': 'BitVec 8', 'a': 'Nat'}
        dvars, merged = [], {}
        for key, f in fa.items():
            if f.text == fb[key].text:
                merged[key] = f
                continue
            d = f"d{kk}_{key}"
            dvars.append((d, types[key[0]], f.rhs, fb[key].rhs))
            lhs = top_split(f.text, ' = ')[0]
            merged[key] = Fact(key, f"{lhs} = {d}")
        branches = []
        for i, (st, args, names, pats, sc, prev, tc) in enumerate(runs):
            parts = list(sc) + [f"{d} = {(va, vb)[i]}" for d, _, va, vb in dvars]
            branches.append(" ∧ ".join(parts) if parts else "True")
        dbind = "".join(f"∃ {d} : {t}, " for d, t, _, _ in dvars)
        part = f"{dbind}(({branches[0]}) ∨ ({branches[1]}))"
        facts = [f for key, f in merged.items() if key != 'STEPS']
        body = " ∧\n        ".join(re.sub(rf"(?<![\w.'])n{kk}(?![\w'])", "n'", f.text) for f in facts)
        P(f"  have M{kk} : SvErrRet B out v n{k} ∨ Panics n{k} ∨ {part} ∧")
        P(f"      ∃ n', Steps n{k} n' ∧\n        {body} := by")
        P(f"    by_cases hb : {runs[0][6]}")
        for i, (st, args, names, pats, sc, prev, tc) in enumerate(runs):
            P(f"    · rcases {args} with ⟨-, e⟩ | ⟨" + ", ".join(names + pats) + "⟩")
            P("      · exact .inr (.inl e)" if st.fail == 'Panics' else "      · exact .inl e")
            pr = names + ["rfl"] * len(dvars) if (sc or dvars) else ["trivial"]
            side = ".inl" if i == 0 else ".inr"
            fpats = [x for x in pats]
            prf = pr[0] if len(pr) == 1 else "⟨" + ", ".join(pr) + "⟩"
            P(f"      exact .inr (.inr ⟨" + "".join(f"{(va, vb)[i]}, " for _, _, va, vb in dvars) +
              f"{side} {prf}, " + ", ".join(fpats) + "⟩)")
        mpats = [f"n{kk}", f"c{kk}"] + [p for f, p in zip(facts, runs[0][3][2:])]
        P(f"  rcases M{kk} with e | e | ⟨" + "".join(f"{d}, " for d, _, _, _ in dvars) + f"x{kk}_m, " +
          ", ".join(mpats) + "⟩")
        self.fail(kk, 'SvErrRet', P)
        self.fail(kk, 'Panics', P)
        self.sc.append(part)
        self.names += [d for d, _, _, _ in dvars] + [f"x{kk}_m"]
        ch.k = kk
        ch.prev = merged

    SIZES = {'w': 4, 'b': 1, 'a': 32}

    def source(self, key, e, j, facts):
        """The fact `key` at step `j`, as a term and its value: stated, or a word
        inside a byte range that step `j` copied from `M0`."""
        if key in facts:
            f = facts[key]
            pre = {'w': 'w0_', 'b': 'b0_', 'a': 'a0_', 'q': 'q0_'}[key[0]]
            return (getattr(f, 'name', None) or (fname(key, j) if j else f"{pre}{key[1:]}"),
                    strip_parens(f.rhs) if f.rhs else None)
        if key[0] != 'w':
            return None
        for k2, f in facts.items():
            if k2[0] != 'q' or k2 == 'q':
                continue
            m = re.fullmatch(r"\(?∀ j, j < (\w+) → \w+\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 \((0x[0-9A-F]+) \+ j\)\) = "
                             r"M0 \((.+) \+ BitVec\.ofNat 32 j\)\)?", f.text)
            if not m:
                continue
            n, c, srcp = int(m.group(1), 0), int(m.group(2), 16), m.group(3)
            if c <= e and e + 4 <= c + n:
                name = fname(k2, j) if j else f"q0_{k2[1:]}"
                d = e - c
                return (f"(memLoad32_of_range (c := 0x{c:X}) (d := {d}) {name} (by decide))",
                        f"memLoad32 M0 ({srcp} + BitVec.ofNat 32 {d})")
        return None

    def carry(self, key, ty):
        """A frame fact that the previous stage doesn't state, from the last stage
        that did, if no stage since wrote its bytes: the term and its value."""
        if key[0] not in 'wbaq' or key == 'KL' or not self.hist:
            return None
        e = int(key[1:], 16)
        if key[0] == 'q':
            m = re.match(r"∀ j, j < (\w+) →", ty)
            if not m:
                return None
            size = int(m.group(1), 0)
        else:
            size = self.SIZES[key[0]]
        for idx in range(len(self.hist) - 1, -1, -1):
            j, facts = self.hist[idx]
            found = self.source(key, e, j, facts)
            if not found:
                continue
            self.found_text = facts[key].text if key in facts else None
            term, val = found
            for i, later in self.hist[idx + 1:]:
                kl = later.get('KL')
                if kl is None:
                    return None
                ranges = [(int(c, 16), int(w, 16)) for c, w in re.findall(r"\(0x([0-9A-F]+), 0x([0-9A-F]+)\)", kl.text)]
                if any(not (e + size <= c or c + w <= e) for c, w in ranges):
                    return None
                K = fname('KL', i)
                if key[0] == 'w':
                    term = f"(({K}.w32 (by decide) (by decide)).trans {term})"
                elif key[0] == 'b':
                    term = f"(({K}.b8 (by decide) (by decide)).trans {term})"
                elif key[0] == 'a':
                    term = f"(({K}.acc (by decide) (by decide)).trans {term})"
                else:
                    term = f"(fun j hj => ({K}.range (by decide) (by decide) j hj).trans ({term} j hj))"
            return term, val
        m = re.fullmatch(r"(memLoad32 n0\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x[0-9A-F]+\)) = (\w+)", ty)
        if m and key[0] == 'w':
            nm = m.group(2)
            taken = {q for q, _ in self.hyps} | set(re.findall(r"[\w']+", self.binders))
            while nm in taken:
                nm += "'"
            self.extra_binders.append(nm)
            hp = f"w0_{key[1:]}"
            while hp in {q for q, _ in self.hyps}:
                hp += "'"
            self.hyps.append((hp, f"{m.group(1)} = {nm}"))
            self.lifted.append(hp)
            self.hist[0][1][key] = Fact(key, f"{m.group(1)} = {nm}")
            self.hist[0][1][key].name = hp
            return self.carry(key, ty)
        return None

    def split_each(self, p, ty):
        """A hypothesis about each of a search's first `N` states, whose parts
        are a counter that isn't 0 yet, facts the segment knows, and facts
        about the start that become a hypothesis of the segment."""
        parts = top_split(ty, ' → ')
        if len(parts) != 3 or not re.fullmatch(r"∀ i, i < \d+", parts[0]):
            return None
        m = re.fullmatch(r"∀ ([\w' ]+), \(([\w', ]+)\) = svIter \(fun s => \((.+)\)\) i \(\(?(.+?)\)?, .+\)", parts[1])
        if not m:
            return None
        cnt = counter(m.group(3), m.group(4))
        vs = m.group(1).split()
        bound = ['i'] + vs
        mentions = lambda t: any(re.search(rf"(?<![\w.']){re.escape(b)}(?![\w'])", t) for b in bound)
        local = r"(?<![\w.'])(n\d+|[\w']+_\d+|d\d+_\w+)(?![\w'])"
        terms, lifted = [], []
        for part in (strip_parens(x) for x in top_split(parts[2], ' ∧ ')):
            if part == f"{vs[0]} ≠ 0" and cnt:
                terms.append(f"(svCnt_ne Prod.fst ({cnt[0]}) 0x{cnt[1]:X} (by intro _; rfl) rfl (by decide) hi "
                             "(congrArg Prod.fst h))")
            elif not mentions(part) and re.search(local, part):
                pf = self.resolve(f"{p}_{len(terms)}", part)
                if pf is None or isinstance(pf, tuple):
                    return None
                terms.append(pf)
            elif mentions(part) and re.search(local, re.sub("|".join(rf"(?<![\w.']){re.escape(b)}(?![\w'])" for b in bound),
                                                            "", part)):
                return None
            else:
                terms.append(None)
                lifted.append(part)
        if not lifted:
            return f"(fun i hi {' '.join(vs)} h => ⟨{', '.join(terms)}⟩)"
        nm = p + "'"
        while nm in {q for q, _ in self.hyps}:
            nm += "'"
        self.hyps.append((nm, f"{parts[0]} → {parts[1]} → " + " ∧ ".join(f"({x})" for x in lifted)))
        self.lifted.append(nm)
        call = f"({nm} i hi {' '.join(vs)} h)"
        j = 0
        for t, x in enumerate(terms):
            if x is None:
                last = j == len(lifted) - 1
                terms[t] = call + ".2" * j + ("" if last else ".1")
                j += 1
        return f"(fun i hi {' '.join(vs)} h => ⟨{', '.join(terms)}⟩)"

    def lift_each(self, p, ty):
        """A hypothesis about the state a search stopped at, from a hypothesis
        of the segment about each state the search can reach."""
        loc = set(re.findall(r"(?<![\w.'])([\w']+_\d+)(?![\w'])", ty))
        if not loc or re.search(r"(?<![\w.'])(n\d+|d\d+_\w+)(?![\w'])", ty):
            return None
        for pf, piece in self.pieces:
            m = re.fullmatch(r"\(([\w', ]+)\) = svIter (.+) ([\w']+) (\(.+\))", canon(strip_exists(piece)))
            if not m:
                continue
            vs = m.group(1).split(', ')
            if not loc <= set(vs):
                continue
            idx = m.group(3)
            lt = next((q for q, x in self.pieces if re.fullmatch(rf"{re.escape(idx)} < (\d+)", canon(strip_exists(x)))), None)
            if not lt:
                continue
            bound = next(re.fullmatch(rf"{re.escape(idx)} < (\d+)", canon(strip_exists(x))).group(1)
                         for q, x in self.pieces if q == lt)
            fresh = [f"y{j}" for j in range(len(vs))]
            body = ty
            for v, f in zip(vs, fresh):
                body = re.sub(rf"(?<![\w.']){re.escape(v)}(?![\w'])", f, body)
            nm = p
            while nm in {q for q, _ in self.hyps}:
                nm += "'"
            self.hyps.append((nm, f"∀ i, i < {bound} → ∀ {' '.join(fresh)}, ({', '.join(fresh)}) = svIter {m.group(2)} i "
                                  f"{m.group(4)} → {body}"))
            self.lifted.append(nm)
            return f"({nm} {idx} {lt} {' '.join(vs)} {pf})"
        return None

    def resolve(self, p, ty, free=()):
        if p in self.extra:
            return self.extra[p]
        hit = self.match_sc(ty, free)
        if hit:
            return hit
        m = re.fullmatch(r"(.+) ≤ (\w+)", strip_parens(ty))
        if m and m.group(2) in free:
            return ("(Nat.le_refl _)", {m.group(2): f"({m.group(1)})"})
        # A counter that starts at a constant and drops by a constant reaches 0
        # after their quotient's steps.
        m = re.fullmatch(r"∀ ([\w' ]+), \(([\w', ]+)\) = svIter \(fun s => \((.+)\)\) (\w+) \(\(?(.+?)\)?, .+\) → (\S+) = 0",
                         strip_parens(ty))
        if m and m.group(4) in free and m.group(6) == m.group(2).split(', ')[0]:
            cnt = counter(m.group(3), m.group(5))
            if cnt:
                c0, d = cnt
                dec, start = 2 ** 32 - d, int(re.search(r"0x[0-9A-F]+", c0).group(0), 16)
                if start % dec == 0:
                    vs = " ".join("_" for _ in m.group(1).split())
                    return (f"(fun {vs} h => svCnt_zero Prod.fst ({c0}) 0x{d:X} (by intro _; rfl) rfl (by decide) "
                            "(congrArg Prod.fst h))", {m.group(4): str(start // dec)})
        hit = self.split_each(p, strip_parens(ty))
        if hit:
            return hit
        m = re.fullmatch(r"(.+) = (.+) \+ BitVec\.ofNat 32 \((\w+) \* 4\)", strip_parens(ty))
        if m and m.group(3) in free:
            terms = split_sum(strip_parens(m.group(1)))
            first = strip_parens(terms[0][1])
            ms = re.fullmatch(r"aluEval \.sll (.+) \(BitVec\.ofNat 32 0x2\)", first)
            rest = " + ".join(t for _, t in terms[1:])
            if ms and len(terms) > 1 and canon(rest) == canon(m.group(2)):
                return ("(by rw [svSll2]; exact BitVec.add_comm _ _)", {m.group(3): f"({strip_parens(ms.group(1))}).toNat"})
        for q, t in self.hyps:
            if q == p and t == ty and not free:
                return p
        local = re.search(r"(?<![\w.'])(n\d+|[\w']+_\d+|d\d+_\w+)(?![\w'])", ty)
        if ty.startswith('SvIn B '):
            ptr, ln = split_in(ty[len('SvIn B '):])
            pf = self.derive_in(ptr, ln)
            if pf:
                return f"({pf})"
        if not local:
            nm = p
            while nm in {q for q, _ in self.hyps}:
                nm += "'"
            self.hyps.append((nm, ty))
            self.lifted.append(nm)
            return nm
        return self.lift_each(p, ty)

    def build(self):
        first = self.stages[0]
        s = open('C3BootProofs/Proofs/' + self.seq[0][0] + '.lean').read()
        i = s.index(f'theorem {first.name} ')
        self.binders = s[i + len(f'theorem {first.name} '):s.index('\n', i)]
        self.hyps = list(first.params)
        self.lifted = []
        self.extra_binders = []
        start = {}
        for p, t in first.params:
            key = param_key(p)
            if key and key[0] in 'wbaq':
                start[key] = Fact(key, t)
        self.hist = [(0, start)]
        self.ins = []
        self.parses = {}
        self.bits = {}
        self.eqs = {}
        self.nl = {}
        self.contents = {}
        self.les = {}
        self.closed = {}
        self.lts = {}
        for p, t in first.params:
            if t.startswith('SvIn B '):
                ptr, ln = split_in(t[len('SvIn B '):])
                self.ins.append((ptr, ln, p))
        proof = []
        P = proof.append
        ch = Chain(P)
        self.sc = []
        self.names = []

        for idx, (kind, st) in enumerate(self.items):
            k = ch.k
            ov = {'F': 'F', 'hret': 'hret', 'hO': 'hO', 'M0': 'M0', 'E0': f'E{k}', 'V0': f'V{k}', 's0': f's{k}',
                  'fM': f'fR{k}'}
            if kind == 'merge':
                self.merge(ch, st, ov, P)
                continue
            if idx == 0:
                ov = {p: p for p, _ in st.params}
            args, names, pats, sc = ch.call(st, ov, resolve=self.resolve, wren=witnesses(st, k + 1),
                                            carry=self.carry)
            self.hist.append((ch.k, dict(ch.prev)))
            self.record(ch.proofs)
            self.sc += sc
            self.names += names
            P(f"  rcases {'@' if ch.at else ''}{st.name} " + " ".join(args) + f" with {st.errpat} | ⟨" + ", ".join(names + pats) + "⟩")
            self.fail(ch.k, st.fail, P)
        self.panics = any(it[1].fail in ('Panics', 'Both') for it in self.items if it[0] == 'stage')
        self.hide_loads()
        self.carried = []
        # Every frame fact that a stage states and no later stage writes over.
        stated = {}
        for p, t in first.params:
            key = param_key(p)
            if key:
                stated[key] = t
        for _, facts in self.hist[1:]:
            for key, f in facts.items():
                stated.setdefault(key, f.text)
        for key, t in stated.items():
            if key[0] not in 'wbq' or key in ch.prev or len(self.hist) < 2:
                continue
            c = self.carry(key, t)
            if c and self.found_text:
                if len(re.findall(r"(?<![\w.'])n\d+(?![\w'])", self.found_text)) != 1:
                    continue
                text = re.sub(r"(?<![\w.'])n\d+(?![\w'])", "n'", strip_parens(self.found_text))
                self.carried.append((key, f"({text})" if text.startswith('∀') else text, c[0]))
        self.ch = ch
        self.proof = proof
        K = ch.k
        self.keep = []
        for key, f in ch.prev.items():
            if key in ('STEPS', 'ST', 'E', 'V', 'FR', 'r3', 'r4'):
                continue
            t = re.sub(rf"(?<![\w.'])n{K}(?![\w'])", "m'", f.text)
            if re.search(r"(?<![\w.'])n[1-9]\d*(?![\w'])", t):
                continue
            self.keep.append((key, t))
        self.end = re.search(r"0x[0-9A-F]+", ch.prev['ST'].text).group(0)
        return self

    def hide_loads(self):
        """A success condition that names a frame word of a machine inside the
        segment, which no stage stated, has that word as a witness instead."""
        load = r"memLoad32 n\d+\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x[0-9A-F]+\)"
        names, at, sc, u = list(self.names), 0, [], 0
        for part in self.sc:
            terms = list(dict.fromkeys(re.findall(load, part)))
            if terms:
                us = [f"u{u + j}" for j in range(len(terms))]
                u += len(terms)
                for t, v in zip(terms, us):
                    part = part.replace(t, v)
                part = f"∃ {' '.join(us)}, {part}"
                names[at:at] = [f"({t})" for t in terms]
            at += part_count(part)
            sc.append(part)
        self.sc, self.names = sc, names

    def union_kl(self):
        out = []
        for _, facts in self.hist[1:]:
            out += [r for r in re.findall(r"\(0x[0-9A-F]+, 0x[0-9A-F]+\)", facts['KL'].text) if r not in out]
        return "[" + ", ".join(out) + "]"

    def statement(self):
        extra = f" {{{' '.join(self.extra_binders)} : Word}}" if self.extra_binders else ""
        out = [f"theorem {self.name} BINDERS"]
        out += [f"    ({p} : {t})" for p, t in self.hyps]
        out[-1] += " :"
        out.append("    SvErrRet B out v n0 ∨ Panics n0 ∨" if self.panics else "    SvErrRet B out v n0 ∨")
        lines = [f"{x} ∧" for x in self.sc] + ["∃ n', Steps n0 n' ∧"]
        out.append("    (" + lines[0])
        out += ["      " + x if x != lines[-1] else "    " + x for x in lines[1:]]
        facts = ["(∀ x, SvR B x → n'.mem x = M0 x)", f"St n'.mem SV n' {self.end} (reg n')", "SvCode n'.mem",
                 "SvSaves B n'.mem v", "reg n' (3 : Fin 32) = reg n0 (3 : Fin 32)",
                 "reg n' (4 : Fin 32) = reg n0 (4 : Fin 32)"]
        facts += [t.replace("m'", "n'") for _, t in self.keep]
        facts += [t for _, t, _ in self.carried]
        facts.append(f"SvKeepL B n0.mem n'.mem {self.union_kl()}")
        out += [f"        {t}" + (" ∧" if j + 1 < len(facts) else ")") for j, t in enumerate(facts)]
        text = "\n".join(out)
        groups_ = []
        for g in re.findall(r"\{([^}]*)\}", self.binders + extra):
            names, ty = g.rsplit(' : ', 1)
            keep = [x for x in names.split() if re.search(rf"(?<![\w.']){re.escape(x)}(?![\w'])", text)]
            if keep:
                groups_.append("{" + " ".join(keep) + " : " + ty + "}")
        return text.replace("BINDERS", " ".join(groups_), 1)

    def lean(self):
        K = self.ch.k
        r3 = ", ".join(f"r{j}_3" for j in range(K, 0, -1))
        r4 = ", ".join(f"r{j}_4" for j in range(K, 0, -1))
        out = ["set_option maxHeartbeats 64000000 in", f"/-- {self.doc} -/", self.statement() + " := by"]
        out += self.proof
        pn = [fname(key, K) for key, _ in self.keep]
        kl = "K1_L"
        for k in range(2, K + 1):
            kl = f"({kl}).trans K{k}_L"
        wrap = (".inr (.inr ", ")") if self.panics else (".inr ", "")
        out.append(f"  exact {wrap[0]}⟨" + ", ".join(self.names) + f", n{K}, {chain_steps(K)}, fR{K}, s{K}, E{K}, V{K},")
        out.append(f"    by rw [{r3}], by rw [{r4}]" + "".join(f", {x}" for x in pn) +
                   "".join(f", {term}" for _, _, term in self.carried) + f", ({kl}).mono (by decide)⟩{wrap[1]}")
        return "\n".join(out)
