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

GLOBAL = ('F', 'hret', 'hO', 'M0')
HEAD_EXTRA = ('E0', 'V0', 's0', 'fM')


class Loop:
    def __init__(self, sfile, sname):
        self.sfile, self.sname = sfile, sname
        st = self.st = Stage(sfile, sname)
        src = self.src = open(f'C3BootProofs/Proofs/{sfile}.lean').read()
        i = src.index(f'theorem {sname} ')
        header = src[i + len(f'theorem {sname} '):src.index('(F : ', i)].strip()
        self.binders = []
        for g in groups(header, '{', '}'):
            names, ty = g.rsplit(' : ', 1)
            self.binders.append((names.split(), ty))
        bset = self.bset = {b for names, _ in self.binders for b in names}
        self.head = [(p, t) for p, t in st.params if p in HEAD_EXTRA or param_key(p)]
        self.per = [(p, t) for p, t in st.params if p not in GLOBAL and (p, t) not in self.head]
        facts = self.facts = {f.key: f for f in st.facts}
        upd = self.upd = {}
        for p, t in self.head:
            key = param_key(p)
            if not key:
                continue
            rhs = strip_parens(top_split(t, ' = ')[-1])
            f = facts.get(key) or facts.get('ra' + key[2:] if re.fullmatch(r'r1[0-7]', key) else '')
            if f is None:
                raise ValueError(f"{sname} doesn't keep {p}")
            if f.rhs is None or len(top_split(t, ' = ')) != 2:
                if strip_parens(re.sub(r"n'", "n0", f.text)) != strip_parens(t):
                    raise ValueError(f"{sname} changes {p}")
                continue
            new = strip_parens(f.rhs)
            if new != rhs:
                if rhs not in bset or rhs in upd:
                    raise ValueError(f"{p}: {rhs} -> {new}")
                upd[rhs] = new
        head_text = " ".join(t for _, t in self.head)
        self.local = {}
        self.kept_per = []
        for p, t in self.per:
            parts = top_split(t, ' = ')
            rhs = strip_parens(parts[-1]) if len(parts) == 2 else None
            if (rhs in bset and rhs not in upd and rhs not in self.local
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
