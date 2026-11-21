"""Composes the generated stages of `sigstore::verify`.

`Stage` reads a stage theorem: its binders, its hypotheses, its success
condition, and its conclusion facts. `Chain` passes each stage the
conclusions of the one before it, by name, and works out what each stage's
binders stand for, the way Lean's unifier does when a hypothesis's
right-hand side is a binder, so that the composed theorem can state its
conclusion in the first stage's terms.
"""

import re

BASE = 'C3BootProofs/Proofs/'
IDENT = r"(?<![\w.'])({})(?![\w'])"


def top_split(s, sep):
    """Splits `s` at `sep` outside parentheses and brackets."""
    out, depth, cur, i = [], 0, '', 0
    while i < len(s):
        c = s[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append(cur)
            cur = ''
            i += len(sep)
            continue
        cur += c
        i += 1
    out.append(cur)
    return out


def groups(s, op='(', cl=')'):
    """The top-level `(...)` groups of `s`."""
    out, depth, start = [], 0, None
    for i, c in enumerate(s):
        if c == op:
            if depth == 0:
                start = i
            depth += 1
        elif c == cl:
            depth -= 1
            if depth == 0:
                out.append(s[start + 1:i])
    return out


def strip_parens(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')') and len(groups(s)) == 1 and groups(s)[0] == s[1:-1]:
        s = s[1:-1].strip()
    return s


class Fact:
    def __init__(self, key, text):
        self.key = key
        self.text = text

    @property
    def rhs(self):
        parts = top_split(self.text, ' = ')
        return parts[-1].strip() if len(parts) >= 2 else None


def fact_key(l):
    if l.startswith("Steps"):
        return 'STEPS'
    if re.match(r"St n'\.mem SV n' 0x", l):
        return 'ST'
    for pre, nm in (("SvCode", 'E'), ("SvSaves", 'V'), ("(∀ x, SvR", 'FR'), ("reg n' sp", 'r2')):
        if l.startswith(pre):
            return nm
    m = re.match(r"reg n' \((\d+) : Fin 32\)", l) or re.match(r"reg n' (a\d)", l)
    if m:
        return 'r' + m.group(1)
    for pre, nm in (("memLoad32 n'\\.mem", 'w'), ("n'\\.mem", 'b'), ("accV n'\\.mem", 'a')):
        m = re.match(pre + r" \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x([0-9A-F]+)\)", l)
        if m:
            return nm + m.group(1).lower()
    m = re.match(r"\(∀ j, j < \d+ → n'\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 \(0x([0-9A-F]+) \+ j\)\)", l)
    if m:
        return 'q' + m.group(1).lower()
    m = re.match(r"ptF n'\.mem B 0x([0-9A-F]+)", l)
    if m:
        return 'p' + m.group(1).lower()
    m = re.match(r"memBytes n'\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x([0-9A-F]+)\)", l)
    if m:
        return 'mb' + m.group(1).lower()
    m = re.match(r"leN \(memBytes n'\.mem \(B \+ 0x21A0 \+ BitVec\.ofNat 32 0x([0-9A-F]+)\)", l)
    if m:
        return 'ln' + m.group(1).lower()
    return None


DEFAULTS = {'Word': '0', 'Bytes': '[]', 'BitVec 8': '0', 'Nat': '0', 'Int': '0', 'Pt2': '(0, 0, 0)'}

PARAM_KEY = {'g0_': 'r', 'w0_': 'w', 'a0_': 'a', 'b0_': 'b', 'q0_': 'q', 'p0_': 'p', 'mb0_': 'mb'}


def param_key(p):
    for pre, k in PARAM_KEY.items():
        if p.startswith(pre):
            return k + p[len(pre):]
    return None


class Stage:
    def __init__(self, fn, name):
        s = open(BASE + fn + '.lean').read()
        i = s.index(f'theorem {name} ')
        j = s.index(':= by\n', i)
        st = s[i:j]
        self.name = name
        hdr_end = st.index('\n')
        self.binders = []
        for g in groups(st[:hdr_end], '{', '}'):
            names, ty = g.rsplit(' : ', 1)
            for n in names.split():
                self.binders.append((n, ty.strip()))
        k = st.index('\n    (¬')
        self.params = []
        for g in groups(st[hdr_end:k]):
            pn, ty = g.split(' : ', 1)
            self.params.append((pn.strip(), ty.strip()))
        neg = st[k + len('\n    (¬ ('):]
        e = min(x for x in (neg.find(') ∧ SvErrRet'), neg.find(') ∧ Panics')) if x >= 0)
        self.sc = neg[:e]
        self.fail = 'Panics' if neg[e:].startswith(') ∧ Panics') else 'SvErrRet'
        rest = st[k:].split('\n')[2:]
        self.nsc = next(i for i, l in enumerate(rest) if "∃ n', Steps" in l)
        self.sc_parts = [l.strip().rstrip('∧').strip() for l in rest[:self.nsc]]
        if self.sc_parts:
            self.sc_parts[0] = self.sc_parts[0][1:]
        body = "\n".join(rest[self.nsc:])
        body = body[body.index("∃ n', ") + len("∃ n', "):]
        body = body.rstrip()
        while body.endswith(')') and body.count(')') > body.count('('):
            body = body[:-1]
        self.facts = []
        for l in body.split('\n'):
            l = l.strip().rstrip('∧').strip()
            if l.startswith('Steps n0 n\' ∧'):
                l = "Steps n0 n'"
            key = fact_key(l)
            if key is None:
                raise ValueError(f"{name}: {l}")
            self.facts.append(Fact(key, l))

    def binder_set(self):
        return {n for n, _ in self.binders}


def subst(text, env):
    if not env:
        return text
    pat = re.compile(IDENT.format("|".join(sorted(map(re.escape, env), key=len, reverse=True))))
    return pat.sub(lambda m: env[m.group(1)] if env[m.group(1)].replace('_', '').isalnum()
                   else "(" + env[m.group(1)] + ")", text)


class Chain:
    """Passes each stage the facts of the one before it."""

    def __init__(self, emit):
        self.emit = emit
        self.k = 0
        self.prev = {}

    def call(self, stage, overrides, fixed=None, resolve=None, wren=None):
        """Emits nothing; returns the arguments for `stage` at step `k + 1`,
        the names for its success condition's witnesses and proofs, the
        names for its facts, and its success condition's parts, all
        instantiated.

        Hypotheses come from `overrides`, then from the previous stage's
        facts by name. A hypothesis about a binder that no fact gives is
        `rfl`. `resolve(name, instantiated type)` gives the rest."""
        k = self.k + 1
        env = dict(fixed or {})
        wren = wren or {}
        env.update(wren)
        bs = stage.binder_set()
        got = {}
        pending = []
        for pn, ty in stage.params:
            parts = top_split(ty, ' = ')
            rhs = strip_parens(parts[-1])
            if pn in overrides:
                got[pn] = overrides[pn]
                if overrides[pn] == 'rfl' and len(parts) == 2 and rhs in bs and rhs not in env:
                    lhs = strip_parens(parts[0])
                    env[rhs] = re.sub(IDENT.format("n0"), f"n{self.k}", lhs) if self.k else lhs
                continue
            key = param_key(pn)
            if key and key.startswith('mb') and ty.startswith('leN'):
                key = 'ln' + key[2:]
            if key and key not in self.prev and re.fullmatch(r'r1[0-7]', key):
                key = 'ra' + key[2]
            if key and key in self.prev:
                f = self.prev[key]
                got[pn] = fname(f.key, self.k)
                if rhs in bs and rhs not in env:
                    env[rhs] = strip_parens(f.rhs)
            elif key and len(parts) == 2 and rhs in bs and rhs not in env:
                got[pn] = 'rfl'
                lhs = strip_parens(parts[0])
                env[rhs] = re.sub(IDENT.format("n0"), f"n{self.k}", lhs) if self.k else lhs
            else:
                pending.append((pn, ty))
        for pn, ty in pending:
            t = re.sub(IDENT.format("n0"), f"n{self.k}", ty) if self.k else ty
            a = resolve(pn, subst(t, env)) if resolve else None
            if a is None:
                raise ValueError(f"{stage.name}: no argument for {pn} : {subst(t, env)}")
            got[pn] = a
        args = [got[pn] for pn, _ in stage.params]
        used = " ".join(ty for _, ty in stage.params)
        last = {b: i for i, (b, _) in enumerate(stage.binders)}
        bargs = []
        for i, (b, ty) in enumerate(stage.binders):
            if last[b] == i and re.search(IDENT.format(re.escape(b)), used):
                bargs.append('_')
            else:
                bargs.append(DEFAULTS.get(ty, '_'))
                if last[b] == i and ty in DEFAULTS:
                    env.setdefault(b, DEFAULTS[ty])
        args = bargs + args
        names = []
        proofs = []
        n = 0
        for part in stage.sc_parts:
            for piece in top_split(part, ' ∧ '):
                piece = piece.strip()
                while piece.startswith('∃ '):
                    c = piece.index(',')
                    names += [wren.get(b, f"x{k}_{n}{b}") for b in piece[2:c].split()]
                    piece = piece[c + 1:].strip()
                names.append(f"x{k}_{n}")
                proofs.append((f"x{k}_{n}", piece))
                n += 1
        pats = []
        facts = {}
        for f in stage.facts:
            if f.key == 'STEPS':
                pats += [f"n{k}", f"c{k}"]
            elif f.key in ('ST', 'E', 'V', 'FR'):
                pats.append({'ST': 's', 'E': 'E', 'V': 'V', 'FR': 'fR'}[f.key] + str(k))
            else:
                pats.append(fname(f.key, k))
            t = re.sub(IDENT.format("n0"), f"n{k - 1}", f.text).replace("n'", f"n{k}")
            t = subst(t, env)
            facts[f.key] = Fact(f.key, t)
        self.env = env
        self.k = k
        self.prev = facts
        sc = [subst(p, env) for p in stage.sc_parts]
        self.proofs = [(nm, subst(t, env)) for nm, t in proofs]
        return args, names, pats, sc


def fname(key, k):
    """The name of fact `key` of step `k` in the generated proofs."""
    return f"{key[0] if key[0] != 'm' else 'mb'}{k}_{key[1:] if key[0] != 'm' else key[2:]}"
