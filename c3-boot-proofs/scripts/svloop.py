"""What a generated stage that returns to its own start says about a loop.

The stage's hypotheses about the machine (registers, frame words, code,
saves, and the frame outside the stack) are the loop's invariant. The
binders that the stage's facts change are the loop's variables; one step
of the loop is a function of the tuple of them. The stage's other
hypotheses hold for each iteration's values. Binders that only those name,
each set by one of them to a read of memory, are replaced by that read.
"""

import re

from svchain import IDENT, Stage, groups, param_key, strip_parens, subst, top_split
from svseg import canon, strip_exists

GLOBAL = ('FW', 'hret', 'hO', 'M0')
HEAD_EXTRA = ('E0', 'V0', 's0', 'fM')


class Loop:
    def __init__(self, sfile, sname):
        self.sfile, self.sname = sfile, sname
        st = self.st = Stage(sfile, sname)
        src = self.src = open(f'C3BootProofs/Proofs/{sfile}.lean').read()
        i = src.index(f'theorem {sname} ')
        header = src[i + len(f'theorem {sname} '):src.index('(FW : ', i)].strip()
        self.binders = []
        for g in groups(header, '{', '}'):
            names, ty = g.rsplit(' : ', 1)
            self.binders.append((names.split(), ty))
        bset = self.bset = {b for names, _ in self.binders for b in names}
        self.head = [(p, t) for p, t in st.params if p in HEAD_EXTRA or param_key(p)]
        self.per = [(p, t) for p, t in st.params if p not in GLOBAL and (p, t) not in self.head]
        facts = self.facts = {f.key: f for f in st.facts}
        upd = self.upd = {}
        types = {}
        for names, ty in self.binders:
            for b in names:
                types[b] = ty
        self.types = types
        # A head register whose binder nothing else names, and that the body
        # overwrites, is dead at the head: each iteration reads it afresh.
        dead = {}
        for p, t in self.head:
            key, parts = param_key(p), top_split(t, ' = ')
            if not key or not key.startswith('r') or len(parts) != 2:
                continue
            rhs, f = strip_parens(parts[-1]), facts.get(key)
            if not re.fullmatch(r"\w+", rhs) or f is None or f.rhs is None:
                continue
            rx = IDENT.format(re.escape(rhs))
            others = [t2 for p2, t2 in st.params if p2 != p] + [g.text for g in st.facts] + st.sc_parts
            if not any(re.search(rx, x) for x in others):
                dead[p] = (rhs, strip_parens(parts[0]))
        self.head = [(p, t) for p, t in self.head if p not in dead]
        self.per = [(p, t) for p, t in st.params if p not in GLOBAL and (p, t) not in self.head]
        for p, t in self.head:
            key = param_key(p)
            if not key:
                continue
            rhs = strip_parens(top_split(t, ' = ')[-1])
            f = facts.get(key) or facts.get('ra' + key[2:] if re.fullmatch(r'r1[0-7]', key) else '')
            if f is None:
                raise ValueError(f"{sname} doesn't keep {p}")
            if f.rhs is None or len(top_split(t, ' = ')) != 2:
                old_t, new_t = strip_parens(t), strip_parens(re.sub(r"n'", "n0", f.text))
                if new_t != old_t and not self.learn(old_t, new_t, bset):
                    raise ValueError(f"{sname} changes {p}")
                continue
            new = strip_parens(f.rhs)
            if new != rhs:
                if rhs in bset and rhs not in upd:
                    upd[rhs] = new
                elif not self.learn(rhs, new, bset):
                    raise ValueError(f"{p}: {rhs} -> {new}")
        head_text = " ".join(t for _, t in self.head)
        self.local = {}
        self.kept_per = []
        for p, t in self.per:
            parts = top_split(t, ' = ')
            rhs = strip_parens(parts[-1]) if len(parts) == 2 else None
            if p in dead or (rhs in bset and rhs not in upd and rhs not in self.local
                             and not re.search(IDENT.format(re.escape(rhs)), head_text)):
                self.local[rhs] = strip_parens(parts[0])
            else:
                self.kept_per.append((p, t))
        self.loopv = loopv = list(upd)
        proj = {b: "s" + ".2" * j + (".1" if j + 1 < len(loopv) else "") for j, b in enumerate(loopv)}
        if len(loopv) == 1:
            proj = {loopv[0]: "s"}
        self.step = "fun s => " + (
            "(" + ", ".join(subst(subst(upd[b], self.local), proj) for b in loopv) + ")" if len(loopv) > 1
            else subst(subst(upd[loopv[0]], self.local), proj))
        self.prime = {b: b + "'" for b in loopv}
        self.fixed = []
        for names, ty in self.binders:
            keep = [b for b in names if b not in upd and b not in self.local and b != 'n0']
            if keep:
                self.fixed.append("{" + " ".join(keep) + " : " + ty + "}")
        self.kl = re.search(r"\[.*\]", facts['KL'].text).group(0)

    def learn(self, old, new, bset):
        """Learns the new value of a binder from an expression `old` that names
        it and the same expression `new` with the value in its place."""
        for b in sorted(bset, key=len, reverse=True):
            rx = rf"(?<![\w.']){re.escape(b)}(?![\w'])"
            if not re.search(rx, old):
                continue
            pat = re.sub(rf"(?<![\w.']){re.escape(re.escape(b))}(?![\w'])", lambda _: "(.+?)", re.escape(old))
            m = re.fullmatch(pat, new)
            if m and len(set(m.groups())) == 1 and m.group(1) != b:
                v = m.group(1)
                if self.upd.get(b, v) != v:
                    return False
                self.upd[b] = v
                return True
        return False

    def tup(self, vs=None):
        vs = vs or self.loopv
        return f"({', '.join(vs)})" if len(vs) > 1 else vs[0]

    def it(self, K, vs=None):
        return f"svIter ({self.step}) {K} {self.tup(vs)}"

    def peq(self, K):
        """The primed loop variables are the values after `K` iterations."""
        return f"{self.tup(list(self.prime.values()))} = {self.it(K)}"

    def primed(self, t, mach=None):
        """`t` at the primed loop variables, on machine `mach`."""
        t = subst(subst(t, self.local), self.prime)
        return re.sub(IDENT.format("n0"), mach, t) if mach else t

    def opens(self):
        for line in self.src.split('\n'):
            if line.startswith('open '):
                return line
        return ""

    def named(self):
        names = [b for ns, _ in self.binders for b in ns if b not in self.local and b != 'n0']
        return " ".join(f"({b} := {b})" for b in dict.fromkeys(names))

    def args(self, extra=None):
        """`st`'s arguments where each hypothesis is its own name, and each
        per-iteration definition of a binder is `rfl`."""
        extra = extra or {}
        out = []
        for p, t in self.st.params:
            if p in extra:
                out.append(extra[p])
            elif (p, t) in self.per and (p, t) not in self.kept_per:
                out.append("rfl")
            else:
                out.append(p)
        return out


def invariants(L, proofs):
    """The hypotheses that a loop variable is 0 or a slice: each one's name,
    type, and the body's proof of it for the variable's next value."""
    out = []
    for p, t in L.kept_per:
        m = re.fullmatch(r"(\w+) = 0 ∨ SvIn B \1 (.+)", t)
        if not m or m.group(1) not in L.loopv:
            continue
        want = canon(subst(t, {b: L.upd[b] for b in L.loopv}))
        nm = next((n for n, piece in proofs if canon(strip_exists(piece)) == want), None)
        if nm is None:
            raise ValueError(f"{L.sname}: nothing keeps {p}")
        out.append((p, t, nm))
    return out
