#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/ScalarMontBody.lean: the straight-line body of
curve25519_dalek's `Scalar29::montgomery_mul`, as compiled, from its first
instruction after the register saves to the stores of the reduced limbs.

The body is `mul_internal` (Karatsuba on the nine 29-bit limbs) and
`montgomery_reduce`, inlined: 1,100 instructions with no branches. Like
gen-fe25519.py, it steps each instruction with a fresh name for its result,
in theorems of 40 instructions each, and turns each result into a
natural-number fact. Each value the Rust source computes is a Lean
definition over the values it is computed from (`smm...`), so no
definition unfolds into more than one step. Running the block and the Rust
source side by side on random inputs finds the words that hold each value;
for each value held in words, one `omega` lemma states those words in terms
of the words of its operands. Values the compiled code never forms whole
(such as `z[8]`) are inlined into the values computed from them.

Run it from c3-boot-proofs/ after ScalarMontDecode.lean changes; CI checks
that the committed file matches.
"""
import importlib.util
import os
import random
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')
_spec = importlib.util.spec_from_file_location('gfe', os.path.join(HERE, 'gen-fe25519.py'))
gfe = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gfe)

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
LFACTOR = 0x12547E1B
L = [0x1CF5D3ED, 0x009318D2, 0x1DE73596, 0x1DF3BD45, 0x0000014D, 0, 0, 0, 0x00100000]
START, END = 0x34, 0xD94
KEEP_SLOTS = [0x15C + 4 * i for i in range(13)]
OUT_REGS = [12, 13, 14, 15, 5, 16, 9, 17, 10]
SEG_CHARS_PER_FILE = 160000
MAX_STORES = 6
LEMMAS_PER_FILE = 70

_alu = gfe.alu


def alu(op, a, b):
    if op == 'sub':
        return (a - b) & M32
    return _alu(op, a, b)


gfe.alu = alu


def decode():
    src = open(os.path.join(ROOT, 'C3BootProofs/Proofs/ScalarMontDecode.lean')).read()
    ins = []
    for m in re.finditer(r'theorem (smm_at_\w+) : fetchRel scalar29MontMulCode (0x[0-9A-Fa-f]+) = '
                         r'some \((.*), (\d)\) := by decide', src):
        ins.append((int(m.group(2), 16), m.group(1), m.group(3), int(m.group(4))))
    ins.sort()
    return [gfe.Ins(*t) for t in ins]


class Gen(gfe.Gen):
    """gen-fe25519's stepper, with facts for `sub` and the 29-bit mask."""

    def seg_bounds(self, n, seg):
        """Each `seg` instructions, split further so that no segment has more
        than MAX_STORES stores: every slot a segment carries is read back
        through each of its stores, and a segment with 18 stores took 7 GB."""
        out = []
        for b in list(range(0, n, seg)):
            e = min(b + seg, n)
            out.append(b)
            cnt = 0
            for k in range(b, e):
                if self.block[k].kind == 'store':
                    cnt += 1
                    if cnt > MAX_STORES and k > out[-1]:
                        out.append(k)
                        cnt = 1
        return out + [n]

    def facts(self):
        self.const = {}
        self.stmt = {}
        for k, i in enumerate(self.block):
            if self.var[k] is None:
                continue
            v = f'v{k}'
            ops = self.src[k]
            if i.kind == 'lui':
                self.const[v] = i.imm
            elif i.kind == 'aluImm' and i.op == 'add' and (i.rs1 == 0 or ops[0] in self.const):
                self.const[v] = ((0 if i.rs1 == 0 else self.const[ops[0]]) + i.imm) & M32
            if v in self.const:
                prevs = [o for o in ops if o in self.const]
                rw = ', '.join(['← hv%d' % k] + ['c' + o[1:] for o in prevs])
                self.emit(f'  have c{k} : {v} = 0x{self.const[v]:X} := by rw [{rw}]; try rfl')
                self.stmt[k] = f'{v}.toNat = {self.const[v]}'
                self.emit(f'  have t{k} : {self.stmt[k]} := by rw [c{k}]; rfl')
                continue
            if i.kind == 'load':
                continue
            a = ops[0]
            if i.kind == 'aluImm':
                sh = i.imm & 31
                if i.op == 'sll':
                    st, pf = f'{v}.toNat = {a}.toNat * 2 ^ {sh} % 2 ^ 32', f'tn_sll hv{k}'
                elif i.op == 'srl':
                    st, pf = f'{v}.toNat = {a}.toNat / 2 ^ {sh}', f'tn_srl hv{k}'
                elif i.op == 'add':
                    st, pf = f'{v}.toNat = ({a}.toNat + {i.imm}) % 2 ^ 32', f'tn_add hv{k}'
                else:
                    raise Exception(i.text)
            else:
                b = ops[1]
                if i.op == 'add':
                    st, pf = f'{v}.toNat = ({a}.toNat + {b}.toNat) % 2 ^ 32', f'tn_add hv{k}'
                elif i.op == 'sub':
                    st, pf = f'{v}.toNat = ({a}.toNat + 2 ^ 32 - {b}.toNat) % 2 ^ 32', f'smm_tn_sub hv{k}'
                elif i.op == 'sltu':
                    st = f'({a}.toNat < {b}.toNat ∧ {v}.toNat = 1) ∨ ({b}.toNat ≤ {a}.toNat ∧ {v}.toNat = 0)'
                    pf = f'tn_sltu hv{k}'
                    if a in self.var:
                        ka = self.var.index(a)
                        ia = self.block[ka]
                        if ia.kind == 'alu' and ia.op == 'add' and b in self.src[ka]:
                            p0, p1 = self.src[ka]
                            st = f'{a}.toNat + 2 ^ 32 * {v}.toNat = {p0}.toNat + {p1}.toNat'
                            pf = f'fmP1 hv{ka} (.{"inl" if b == p0 else "inr"} hv{k})'
                    if pf.startswith('tn_sltu'):
                        # a subtraction of the same operands: the borrow and the difference together
                        for ks, ib in enumerate(self.block):
                            if (self.var[ks] and ib.kind == 'alu' and ib.op == 'sub' and self.src[ks] == [a, b]):
                                y = self.var[ks]
                                st = f'{y}.toNat + {b}.toNat = {a}.toNat + 2 ^ 32 * {v}.toNat'
                                pf = f'smmS1 hv{ks} hv{k}'
                                break
                elif i.op in ('mul', 'mulhu'):
                    tail = '% 2 ^ 32' if i.op == 'mul' else '/ 2 ^ 32'
                    lem = 'tn_mul' if i.op == 'mul' else 'tn_mulhu'
                    if b in self.const or a in self.const:
                        x, c = (a, b) if b in self.const else (b, a)
                        comm = '' if c == b else ', Nat.mul_comm'
                        st = f'{v}.toNat = {x}.toNat * {self.const[c]} {tail}'
                        pf = f'by rw [{lem} hv{k}, t{c[1:]}{comm}]'
                    else:
                        st, pf = f'{v}.toNat = {a}.toNat * {b}.toNat {tail}', f'{lem} hv{k}'
                elif i.op == 'and':
                    c = b if b in self.const else a
                    if c not in self.const or self.const[c] != 0x1FFFFFFF:
                        raise Exception(i.text)
                    x = a if c == b else b
                    st = f'{v}.toNat = {x}.toNat % 2 ^ 29'
                    pf = f'tn_and29' + ('' if c == b else "'") + f' hv{k} c{c[1:]}'
                elif i.op == 'or':
                    ia, ib = self.block[self.var.index(a)], self.block[self.var.index(b)]
                    if ia.op == 'srl' and ib.op == 'sll':
                        x, y, ix, iy, lem = a, b, ia, ib, 'tn_orS'
                    elif ia.op == 'sll' and ib.op == 'srl':
                        x, y, ix, iy, lem = b, a, ib, ia, "tn_orS'"
                    else:
                        raise Exception(i.text)
                    sh = ix.imm & 31
                    if (iy.imm & 31) != 32 - sh:
                        raise Exception(i.text)
                    st = f'{v}.toNat = {x}.toNat + {y}.toNat'
                    pf = f'{lem} {sh} (by decide) hv{k} t{x[1:]} t{y[1:]}'
                else:
                    raise Exception(i.text)
            self.stmt[k] = st
            self.emit(f'  have t{k} : {st} := {pf}')


class Spec:
    """The Rust values in order. Each has a width (32 or 64 bits), a Lean
    expression with `{Name}` for the values it is computed from, a Python
    function, and its operands."""

    def __init__(self):
        self.vals = []
        self.by = {}

    def add(self, name, bits, expr, fn, deps):
        if name in self.by:
            return name
        self.by[name] = len(self.vals)
        self.vals.append((name, bits, expr, fn, deps))
        return name

    def run(self, inputs):
        env = dict(inputs)
        for name, _, _, fn, _ in self.vals:
            if name not in env:
                env[name] = fn(env)
        return env


class NonLinear(Exception):
    pass


def lin_of(x):
    """`x` as a Lin: a Lin, or a constant."""
    return x if isinstance(x, Lin) else Lin({}, x)


class Lin:
    """A linear combination of symbols with integer coefficients."""

    def __init__(self, d=None, c=0):
        self.d = dict(d or {})
        self.c = c

    def __add__(self, o):
        o = lin_of(o)
        d = dict(self.d)
        for k, v in o.d.items():
            d[k] = d.get(k, 0) + v
        return Lin({k: v for k, v in d.items() if v}, self.c + o.c)

    __radd__ = __add__

    def __neg__(self):
        return Lin({k: -v for k, v in self.d.items()}, -self.c)

    def __sub__(self, o):
        return self + (-lin_of(o))

    def __rsub__(self, o):
        return lin_of(o) - self

    def __mul__(self, o):
        if isinstance(o, Lin):
            if o.d and self.d:
                raise NonLinear()
            if not o.d:
                o = o.c
            else:
                return o * self
        return Lin({k: v * o for k, v in self.d.items() if v * o}, self.c * o)

    __rmul__ = __mul__

    def key(self):
        return (tuple(sorted(self.d.items())), self.c)


def lin_eval(expr, mods, modulus=2 ** 64):
    """`expr` (Lean over `vN.toNat`, `+ - * ^ %`, parentheses) as a Lin; each
    `% modulus` gives the symbol of its operand, from `mods`. `*` and `%` bind
    alike and tighter than `+` and `-`, and `^` tighter still, as in Lean."""
    if '/' in expr:
        raise NonLinear()
    toks = re.findall(r'v\d+\.toNat|\d+|[-+*%^()]', expr)
    if ''.join(toks) != re.sub(r'\s+', '', expr):
        raise NonLinear()
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def take():
        pos[0] += 1
        return toks[pos[0] - 1]

    def atom():
        tk = take()
        if tk == '(':
            v = add()
            take()
            return v
        if tk.endswith('.toNat'):
            return Lin({tk[:-len('.toNat')]: 1}, 0)
        return Lin({}, int(tk))

    def power():
        b = atom()
        if peek() == '^':
            take()
            e = power()
            if b.d or e.d:
                raise NonLinear()
            return Lin({}, b.c ** e.c)
        return b

    def modop(x, m):
        if m.d or m.c != modulus:
            raise NonLinear()
        for name, inner in mods:
            if inner.key() == x.key():
                return Lin({name: 1}, 0)
        raise NonLinear()

    def mul():
        v = power()
        while peek() in ('*', '%'):
            op = take()
            r = power()
            v = v * r if op == '*' else modop(v, r)
        return v

    def add():
        v = mul()
        while peek() in ('+', '-'):
            op = take()
            r = mul()
            v = v + r if op == '+' else v - r
        return v

    return add()


def inner_mods(rhs, bits=64):
    """The subterms `(E) % 2 ^ bits` of `rhs`, innermost first."""
    out = []
    for m in re.finditer(rf' % 2 \^ {bits}\b', rhs):
        j = m.start() - 1
        if rhs[j] != ')':
            continue
        depth = 0
        while j >= 0:
            if rhs[j] == ')':
                depth += 1
            elif rhs[j] == '(':
                depth -= 1
                if depth == 0:
                    break
            j -= 1
        out.append((rhs[j:m.start()], rhs[j:m.end()]))
    out.sort(key=lambda t: len(t[0]))
    return out


def structured_lemma(name, st, hyps, words_of):
    """The proof of a 64-bit sum `lo + 2 ^ 32 * hi = (R) % 2 ^ 64` as an exact
    identity: each `% 2 ^ 32` fact becomes an equation with a quotient, and
    the identity's quotient coefficients come from expanding the words."""
    lhs, rhs = st.split(' = ', 1)
    m = re.fullmatch(r'(v\d+)\.toNat \+ 2 \^ 32 \* (v\d+)\.toNat', lhs)
    if not m or not rhs.endswith(' % 2 ^ 64') or not rhs.startswith('('):
        raise NonLinear()
    lo, hi = m.group(1), m.group(2)
    r0 = rhs[:-len(' % 2 ^ 64')]
    # the definition of each word from the facts
    combined = set()
    for h, t in hyps:
        mm = re.match(r'(v\d+)\.toNat \+ (?:2 \^ 32 \* )?v\d+\.toNat = ', t)
        if mm:
            combined.add(mm.group(1))
    defs, keep, qs = {}, [], []
    defs_text = dict(hyps)
    for h, t in hyps:
        mm = re.fullmatch(r'(v\d+)\.toNat = \((.*)\) % 2 \^ 32', t)
        if mm:
            v = mm.group(1)
            if v in combined:
                continue
            q = f'q{h[1:]}'
            defs[v] = (mm.group(2), q)
            qs.append((h, q))
            continue
        mm = re.fullmatch(r'(v\d+)\.toNat \+ 2 \^ 32 \* (v\d+)\.toNat = (v\d+)\.toNat \+ (v\d+)\.toNat', t)
        if mm:
            defs[mm.group(1)] = (f'{mm.group(3)}.toNat + {mm.group(4)}.toNat - 2 ^ 32 * {mm.group(2)}.toNat', None)
            keep.append(h)
            continue
        mm = re.fullmatch(r'(v\d+)\.toNat \+ (v\d+)\.toNat = (v\d+)\.toNat \+ 2 \^ 32 \* (v\d+)\.toNat', t)
        if mm:
            defs[mm.group(1)] = (f'{mm.group(3)}.toNat + 2 ^ 32 * {mm.group(4)}.toNat - {mm.group(2)}.toNat', None)
            keep.append(h)
            continue
        mm = re.fullmatch(r'(v\d+)\.toNat = (\d+)', t)
        if mm:
            defs[mm.group(1)] = (mm.group(2), None)
            keep.append(h)
            continue
        raise NonLinear()
    cache = {}

    def lin_word(v):
        if v in cache:
            return cache[v]
        if v not in defs:
            r = Lin({v: 1}, 0)
        else:
            e, q = defs[v]
            r = lin_eval(re.sub(r'(v\d+)\.toNat', lambda x: f'({x.group(1)}.toNat)', e), [])
            r = sum((Lin({k: c}, 0) if k not in defs else lin_word(k) * c for k, c in r.d.items()), Lin({}, r.c))
            if q:
                r = r - Lin({q: 2 ** 32}, 0)
        cache[v] = r
        return r

    mods = []
    for j, (inner, whole) in enumerate(inner_mods(r0)):
        mods.append((f'm{j}', lin_eval(inner, [(nm, l) for nm, l, _, _ in mods]), inner, whole))
    total = lin_word(lo) + lin_word(hi) * (2 ** 32)
    rl = lin_eval(r0, [(nm, l) for nm, l, _, _ in mods])
    for nm, l, _, _ in reversed(mods):
        # m = inner - 2^64 k
        c = rl.d.pop(nm, 0)
        if c:
            rl = rl + l * c - Lin({'k' + nm[1:]: 2 ** 64 * c}, 0)
    diff = total - rl
    coef = {}
    for k, c in diff.d.items():
        if k.startswith('q') or (k.startswith('k') and k[1:].isdigit()):
            if c % (2 ** 64):
                raise NonLinear()
            coef[k] = c // 2 ** 64
        else:
            raise NonLinear()
    if diff.c % (2 ** 64):
        raise NonLinear()
    c0 = diff.c // 2 ** 64
    # lo + 2^32 hi = R + 2^64 (sum coef x + c0)
    pos = [f'{c} * {k}' if c != 1 else k for k, c in coef.items() if c > 0] + ([str(c0)] if c0 > 0 else [])
    neg = [f'{-c} * {k}' if c != -1 else k for k, c in coef.items() if c < 0] + ([str(-c0)] if c0 < 0 else [])
    xs = ' + '.join(neg) or '0'
    ys = ' + '.join(pos) or '0'
    hs = [(h, t) for h, t in hyps if h in keep or h in [q[0] for q in qs]]
    wset = set(gfe.WORD_RE.findall(st))
    for _, t in hs:
        wset |= set(gfe.WORD_RE.findall(t))
    words = sorted(wset, key=lambda w: int(w[1:]))
    out = [f'theorem {name} {{{" ".join(words)} : Word}}']
    out.append('    ' + '\n    '.join(f'({h} : {t})' for h, t in hs) + ' :')
    out.append(f'    {st} := by')
    for h, q in qs:
        out.append(f'  obtain ⟨{q}, e{q}⟩ := mod_q {h}; clear {h}')
    for j, (nm, _, inner, whole) in enumerate(mods):
        out.append(f'  obtain ⟨k{j}, ek{j}⟩ : ∃ k, {whole} + 2 ^ 64 * k = {inner} := ⟨_, Nat.mod_add_div _ _⟩')
    # bounds only where a truncated subtraction needs one: omega's search grows with each inequality
    bnd = set()
    for h, q in qs:
        bnd |= set(re.findall(r'\+ 2 \^ 32 - (v\d+)\.toNat', defs_text[h]))
    for mm in re.finditer(r'2 \^ 64 - \(', r0):
        j, depth = mm.end() - 1, 0
        while j < len(r0):
            if r0[j] == '(':
                depth += 1
            elif r0[j] == ')':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        bnd |= set(gfe.WORD_RE.findall(r0[mm.end() - 1:j + 1]))
    lts = ''.join(f'have := {w}.isLt; ' for w in sorted(bnd, key=lambda w: int(w[1:])))
    gen = ''.join(f'\n    generalize {w}.toNat = n{w[1:]} at *' for w in words)
    out.append(f'  have key : {lhs} + 2 ^ 64 * ({xs}) = {r0} + 2 ^ 64 * ({ys}) := by')
    out.append(f'    {lts}clear {" ".join(h for h, _ in hs if h not in [q[0] for q in qs])}' if False else f'    {lts}skip{gen}')
    out.append('    omega')
    out.append(f'  exact smm_key key (smm_lt {lo} {hi})')
    return '\n'.join(out), hs


PROD_RE = re.compile(r'\b(v\d+)\.toNat \* (v\d+)\.toNat\b')


def comm_products(text):
    """`omega` takes each product of words as an atom, so when a lemma
    multiplies two words in both orders, it states that they are equal."""
    pairs = set(PROD_RE.findall(text))
    flips = sorted((a, b) for a, b in pairs if (b, a) in pairs and a < b)
    if not flips:
        return text
    head, sep, rest = text.partition(' := by\n')
    haves = '; '.join(f'have := Nat.mul_comm {a}.toNat {b}.toNat' for a, b in flips)
    return f'{head}{sep}  {haves}\n{rest}'


def build_spec():
    sp = Spec()
    A = [sp.add(f'A{i}', 32, f'a {i}', None, []) for i in range(9)]
    B = [sp.add(f'B{i}', 32, f'b {i}', None, []) for i in range(9)]

    def prod(x, y):
        return sp.add(f'P{x}{y}', 64, f'{{{x}}} * {{{y}}}', lambda e: e[x] * e[y], [x, y])

    def cprod(x, c, j):
        return sp.add(f'P{x}L{j}', 64, f'{{{x}}} * {c}', lambda e: e[x] * c, [x])

    def wsum(name, terms):
        return sp.add(name, 64, '(' + ' + '.join(f'{{{t}}}' for t in terms) + ') % 2 ^ 64',
                      lambda e: sum(e[t] for t in terms) & M64, list(terms))

    def wsub(name, x, y):
        return sp.add(name, 64, f'({{{x}}} + (2 ^ 64 - {{{y}}})) % 2 ^ 64',
                      lambda e: (e[x] - e[y]) & M64, [x, y])

    def add32(name, x, y):
        return sp.add(name, 32, f'({{{x}}} + {{{y}}}) % 2 ^ 32', lambda e: (e[x] + e[y]) & M32, [x, y])

    def pa(i, j):
        return prod(A[i], B[j])

    Z0 = pa(0, 0)
    Z1 = wsum('Z1', [pa(0, 1), pa(1, 0)])
    Z2 = wsum('Z2', [pa(0, 2), pa(1, 1), pa(2, 0)])
    Z3 = wsum('Z3', [pa(0, 3), pa(1, 2), pa(2, 1), pa(3, 0)])
    Z4 = wsum('Z4', [pa(0, 4), pa(1, 3), pa(2, 2), pa(3, 1), pa(4, 0)])
    Z5a = wsum('Z5a', [pa(1, 4), pa(2, 3), pa(3, 2), pa(4, 1)])
    Z6a = wsum('Z6a', [pa(2, 4), pa(3, 3), pa(4, 2)])
    Z7a = wsum('Z7a', [pa(3, 4), pa(4, 3)])
    Z8a = wsub('Z8a', pa(4, 4), Z3)
    Z10a = wsub('Z10a', Z5a, pa(5, 5))
    Z11a = wsub('Z11a', Z6a, wsum('Q11', [pa(5, 6), pa(6, 5)]))
    Z12a = wsub('Z12a', Z7a, wsum('Q12', [pa(5, 7), pa(6, 6), pa(7, 5)]))
    Z13 = wsum('Z13', [pa(5, 8), pa(6, 7), pa(7, 6), pa(8, 5)])
    Z14 = wsum('Z14', [pa(6, 8), pa(7, 7), pa(8, 6)])
    Z15 = wsum('Z15', [pa(7, 8), pa(8, 7)])
    Z16 = pa(8, 8)
    Z5b = wsub('Z5b', Z10a, Z0)
    Z6b = wsub('Z6b', Z11a, Z1)
    Z7b = wsub('Z7b', Z12a, Z2)
    Z8b = wsub('Z8b', Z8a, Z13)
    Z9a = wsum('Z9a', [Z14, Z4])
    Z10b = wsum('Z10b', [Z15, Z10a])
    Z11b = wsum('Z11b', [Z16, Z11a])
    AA = [add32(f'AA{k}', A[k], A[k + 5]) for k in range(4)]
    BB = [add32(f'BB{k}', B[k], B[k + 5]) for k in range(4)]
    Z5 = wsum('Z5', [prod(AA[0], BB[0]), Z5b])
    Z6 = wsum('Z6', [wsum('K6', [prod(AA[0], BB[1]), prod(AA[1], BB[0])]), Z6b])
    Z7 = wsum('Z7', [wsum('K7', [prod(AA[0], BB[2]), prod(AA[1], BB[1]), prod(AA[2], BB[0])]), Z7b])
    Z8 = wsum('Z8', [wsum('K8', [prod(AA[0], BB[3]), prod(AA[1], BB[2]), prod(AA[2], BB[1]),
                                 prod(AA[3], BB[0])]), Z8b])
    Z9 = wsub('Z9', wsum('K9', [prod(AA[0], B[4]), prod(AA[1], BB[3]), prod(AA[2], BB[2]), prod(AA[3], BB[1]),
                                prod(A[4], BB[0])]), Z9a)
    Z10 = wsub('Z10', wsum('K10', [prod(AA[1], B[4]), prod(AA[2], BB[3]), prod(AA[3], BB[2]),
                                   prod(A[4], BB[1])]), Z10b)
    Z11 = wsub('Z11', wsum('K11', [prod(AA[2], B[4]), prod(AA[3], BB[3]), prod(A[4], BB[2])]), Z11b)
    Z12 = wsub('Z12', wsum('K12', [prod(AA[3], B[4]), prod(A[4], BB[3])]), Z12a)
    Z = [Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16]

    N, C, R = [], [], []
    # part1 on S0 = z[0], then on each sum through S8
    S = Z[0]
    for i in range(17):
        if i > 0:
            terms = [C[i - 1], Z[i]]
            for j in range(9):
                k = i - j
                if 0 <= j < len(N) and 1 <= k <= 8 and L[k]:
                    terms.append(cprod(N[j], L[k], k))
            S = wsum(f'S{i}', terms)
        if i < 9:
            n = sp.add(f'N{i}', 32, f'({{{S}}} % 2 ^ 32 * {LFACTOR} % 2 ^ 32) % 2 ^ 29',
                       lambda e, S=S: ((e[S] & M32) * LFACTOR & M32) & ((1 << 29) - 1), [S])
            N.append(n)
            t = wsum(f'T{i}', [S, cprod(n, L[0], 0)])
            C.append(sp.add(f'C{i}', 64, f'{{{t}}} / 2 ^ 29', lambda e, t=t: e[t] >> 29, [t]))
        else:
            R.append(sp.add(f'R{i - 9}', 32, f'{{{S}}} % 2 ^ 29', lambda e, S=S: e[S] & ((1 << 29) - 1), [S]))
            C.append(sp.add(f'C{i}', 64, f'{{{S}}} / 2 ^ 29', lambda e, S=S: e[S] >> 29, [S]))
    R.append(sp.add('R8', 32, f'{{{C[16]}}} % 2 ^ 32', lambda e: e[C[16]] & M32, [C[16]]))
    return sp, A, B, R


def lname(name):
    return f'smv{name}'


def main():
    ins = decode()
    block = [i for i in ins if START <= i.off < END]
    g = Gen(block, 'smm', 'scalar29MontMulCode', START, END,
            {2: 'F', 10: 'outp', 11: 'xp', 12: 'yp', 3: 'G3', 4: 'G4'})
    g.init_hyp = {2: 'hsp', 10: 'ha0', 11: 'ha1', 12: 'ha2', 3: 'hG3', 4: 'hG4'}
    g.basenames = ['outp', 'xp', 'yp', 'G3', 'G4']
    g.global_hyps = ('(hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)\n'
                     '    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) '
                     '(sYF : Sep yp 36 F 0x190)')
    g.global_args = 'hF hx hy sFC sXF sYF'
    g.regions = [('F', 0x190, 'hx', 'sFC', 'hF')]
    g.region_sep = {}
    g.step_seg('smm', {'xp': ('hx', ['sXF']), 'yp': ('hy', ['sYF'])}, 40,
               [('F', o) for o in KEEP_SLOTS], [('F', 0xF8)])
    g.facts()

    sp, A, B, R = build_spec()
    rnd = random.Random(710)
    runs = []
    for t in range(48):
        bits = 29 if t % 2 else 32
        a = [rnd.getrandbits(bits) for _ in range(9)]
        b = [rnd.getrandbits(bits) for _ in range(9)]
        regs0 = [0] * 32
        regs0[2], regs0[10], regs0[11], regs0[12] = 0x10000, 0x3000, 0x2000, 0x2800
        mem = {}
        for k in range(9):
            mem[0x2000 + 4 * k] = a[k]
            mem[0x2800 + 4 * k] = b[k]
        vals, regs = gfe.simulate(block, regs0, mem)
        env = sp.run({**{f'A{i}': a[i] for i in range(9)}, **{f'B{i}': b[i] for i in range(9)}})
        for r_, nm in zip(OUT_REGS, R):
            if regs[r_] != env[nm]:
                raise Exception(f'register {r_} does not hold {nm}')
        runs.append((vals, env))
    n = len(block)

    def find(f):
        for k in range(n):
            v = g.var[k]
            if v is None or v in g.const:
                continue
            if all(vals[k] == f(env) for vals, env in runs):
                return v
        return None

    # the words holding each value
    words = {}
    for i in range(9):
        words[A[i]] = (g.inputs[('xp', 4 * i)],)
        words[B[i]] = (g.inputs[('yp', 4 * i)],)
    for name, bits, _, _, _ in sp.vals:
        if name in words:
            continue
        lo = find(lambda e, name=name: e[name] & M32)
        if bits == 32:
            if lo is not None:
                words[name] = (lo,)
        else:
            hi = find(lambda e, name=name: e[name] >> 32)
            if lo is not None and hi is not None:
                words[name] = (lo, hi)
    for r_, nm in zip(OUT_REGS, R):
        if words.get(nm) != (g.final[r_],):
            words[nm] = (g.final[r_],)

    def we(name):
        """A value's expression over words: its words, or its definition over
        its operands' word expressions when no word holds it."""
        if name in words:
            w = words[name]
            return f'{w[0]}.toNat' if len(w) == 1 else f'({w[0]}.toNat + 2 ^ 32 * {w[1]}.toNat)'
        _, _, expr, _, deps = sp.vals[sp.by[name]]
        return '(' + re.sub(r'\{(\w+)\}', lambda m: we(m.group(1)), expr) + ')'

    def stmt_of(name):
        _, bits, expr, _, _ = sp.vals[sp.by[name]]
        rhs = re.sub(r'\{(\w+)\}', lambda m: we(m.group(1)), expr)
        w = words[name]
        lhs = f'{w[0]}.toNat' if len(w) == 1 else f'{w[0]}.toNat + 2 ^ 32 * {w[1]}.toNat'
        return f'{lhs} = {rhs}'

    lemmas, body = [], []
    earlier = set()
    for name in list(A) + list(B):
        earlier.add(words[name][0])
    wstmt = {}
    for name, bits, expr, _, deps in sp.vals:
        if name in A or name in B or name not in words:
            continue
        st = stmt_of(name)
        used = set(gfe.WORD_RE.findall(st.split(' = ', 1)[1]))
        targets = list(words[name])
        ks, stops = g.cone(targets, (earlier | used) - set(targets))
        hyps = [(f't{k}', g.stmt[k]) for k in ks]
        extra = sorted((s_ for s_ in stops if s_ not in used), key=lambda w: int(w[1:]))
        if extra:
            # a stop outside the operands' words: the fact of an operand that names it
            held = []

            def collect(d):
                if d in words:
                    held.append(d)
                else:
                    for dd in sp.vals[sp.by[d]][4]:
                        collect(dd)
            for d in deps:
                collect(d)
            for e_ in extra:
                for d in held:
                    if d in wstmt and re.search(rf'\b{e_}\b', wstmt[d]) and (f'w{d}', wstmt[d]) not in hyps:
                        hyps.append((f'w{d}', wstmt[d]))
                        break
                else:
                    if not any(re.search(rf'\b{e_}\b', t_) for h_, t_ in hyps if h_.startswith('w')):
                        raise Exception(f'{name}: the cone stops at {e_}, which no operand names')
        wset = set(gfe.WORD_RE.findall(st))
        for _, t_ in hyps:
            wset |= set(gfe.WORD_RE.findall(t_))
        lnm = f'smm_v_{name}'
        try:
            text, hyps = structured_lemma(lnm, st, hyps, wset)
            lemmas.append(comm_products(text))
        except NonLinear:
            lemmas.append(comm_products(gfe.lemma(lnm, st, wset, [], hyps)))
        body.append(f'  have w{name} : {st} := {lnm} ' + ' '.join(h for h, _ in hyps))
        wstmt[name] = st
        earlier |= set(targets)

    # the definitions
    defs = []
    for name, bits, expr, _, deps in sp.vals:
        if name in A or name in B:
            continue
        rhs = re.sub(r'\{(\w+)\}', lambda m: (f'{m.group(1)[0].lower()} {m.group(1)[1:]}'
                                               if m.group(1) in A or m.group(1) in B
                                               else f'{lname(m.group(1))} a b'), expr)
        pa = 'a' if re.search(r'\ba\b', rhs) else '_a'
        pb = 'b' if re.search(r'\bb\b', rhs) else '_b'
        defs.append(f'def {lname(name)} ({pa} {pb} : Nat → Nat) : Nat := {rhs}')

    # each value held in words, by name, from the facts over words
    names_body = []
    for i in range(9):
        for nm, base, w in ((A[i], 'xp', words[A[i]][0]), (B[i], 'yp', words[B[i]][0])):
            names_body.append(f'  have h{nm} : {w}.toNat = smmIn M {base} {i} := by')
            names_body.append(f'    rw [smmIn, ite_eq_left (by decide), ← hv{w[1:]}] <;> rfl')
    for name, bits, expr, _, deps in sp.vals:
        if name in A or name in B or name not in words:
            continue
        w = words[name]
        lhs = f'{w[0]}.toNat' if len(w) == 1 else f'{w[0]}.toNat + 2 ^ 32 * {w[1]}.toNat'
        held = []

        def collect(d):
            if d in words:
                held.append(d)
            else:
                for dd in sp.vals[sp.by[d]][4]:
                    collect(dd)
        for d in deps:
            collect(d)
        rws = []
        held.sort(key=lambda d: -len(words[d]))
        for d in dict.fromkeys(held):
            rws.append(f'h{d}')
        rw = f'rw [w{name}' + ''.join(f', {r_}' for r_ in rws) + ']'
        names_body.append(f'  have h{name} : {lhs} = {lname(name)} (smmIn M xp) (smmIn M yp) := by')
        names_body.append(f'    {rw} <;> rfl')

    # One Lean process holding every segment and lemma peaked above 23 GB, so
    # they go in separate files, each compiled by its own process.
    parts = []

    def part(name, doc, items):
        parts.append(name)
        p = ['import C3BootProofs.Proofs.ScalarMontFacts', '', f'/-! {doc} -/', '',
             'namespace C3.RV32', '', 'open C3.Image', '']
        for t in items:
            p += [t, '']
        p += ['end C3.RV32']
        open(os.path.join(ROOT, f'C3BootProofs/Proofs/{name}.lean'), 'w').write('\n'.join(p) + '\n')

    gen = '`scripts/gen-scalar-mont.py` writes this file.'
    groups, cur = [], []
    for i, t in enumerate(g.seg_thms):
        if cur and sum(len(g.seg_thms[j]) for j in cur) + len(t) > SEG_CHARS_PER_FILE:
            groups.append(cur)
            cur = []
        cur.append(i)
    groups.append(cur)
    for k, grp in enumerate(groups):
        lo, hi = grp[0], grp[-1]
        span = f'segment {lo}' if lo == hi else f'segments {lo} to {hi}'
        part(f'ScalarMontSeg{k}', f'# `montgomery_mul`\'s body, {span}\n\n'
             f'Each theorem steps 40 instructions. {gen}', [g.seg_thms[j] for j in grp])
    for k, lo in enumerate(range(0, len(lemmas), LEMMAS_PER_FILE)):
        part(f'ScalarMontVal{k}',
             f'# `montgomery_mul`\'s values, part {k}\n\n'
             f'Each lemma proves one value the code holds in words from its instructions\' facts. {gen}',
             lemmas[lo:lo + LEMMAS_PER_FILE])

    pdir = os.path.join(ROOT, 'C3BootProofs/Proofs')
    for f in os.listdir(pdir):
        if re.fullmatch(r'ScalarMont(Seg|Val)\d+\.lean', f) and f[:-5] not in parts:
            os.remove(os.path.join(pdir, f))

    o = [f'import C3BootProofs.Proofs.{p}' for p in parts] + ['',
         '/-! # The straight-line body of `Scalar29::montgomery_mul`, as compiled', '',
         '`scripts/gen-scalar-mont.py` writes this file from the decoded instructions:',
         'a definition for each value the Rust source computes, and `smm_body`, which',
         'chains the segment theorems (`ScalarMontSeg*`) and the value lemmas',
         '(`ScalarMontVal*`). -/', '',
         'namespace C3.RV32', '', 'open C3.Image', '']
    o += defs + ['']
    keep = ' ∧\n      '.join(f'memLoad32 M\' (F + 0x{s_:X}) = memLoad32 M (F + 0x{s_:X})' for s_ in KEEP_SLOTS)
    regs = ', '.join(f"reg n' {gfe.lreg(r_)}" for r_ in OUT_REGS)
    outs = ', '.join(f'{lname(nm)} (smmIn M xp) (smmIn M yp)' for nm in R)
    o += ['set_option maxHeartbeats 40000000 in', 'set_option maxRecDepth 100000 in',
          '/-- **The body of `montgomery_mul`**, from 0x34 to the stores of the result at',
          '0xD94: the nine registers it leaves for the stores hold `montgomery_reduce` of',
          '`mul_internal` of the operands\' limbs, it writes nothing outside its frame,',
          'and it leaves the frame slots that hold the saved registers alone. -/',
          'theorem smm_body {M : Word → BitVec 8} {B F outp xp yp : Word} {n : Machine}',
          '    (s : St M B n 0x34 (reg n)) (hc : CodeIn M B scalar29MontMulCode) (hsp : reg n sp = F)',
          '    (ha0 : reg n a0 = outp) (ha1 : reg n a1 = xp) (ha2 : reg n a2 = yp)',
          '    (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)',
          '    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190) :',
          '    ∃ n\' M\', Steps n n\' ∧ St M\' B n\' 0xD94 (reg n\') ∧ (∀ x, Sep F 0x190 x 1 → M\' x = M x) ∧',
          f'      {keep} ∧',
          '      memLoad32 M\' (F + 0xF8) = outp ∧',
          f'      [{regs}].map BitVec.toNat =',
          f'        [{outs}] ∧',
          '      reg n\' sp = F ∧ reg n\' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n\' (4 : Fin 32) = reg n (4 : Fin 32) := by',
          '  obtain ⟨G3, hG3⟩ : ∃ g, reg n (3 : Fin 32) = g := ⟨_, rfl⟩',
          '  obtain ⟨G4, hG4⟩ : ∃ g, reg n (4 : Fin 32) = g := ⟨_, rfl⟩']
    o += g.lines
    o += body
    o += names_body
    steps = g.steps_final
    chain = steps[-1]
    for c in reversed(steps[:-1]):
        chain = f'{c}.trans ({chain})'
    last = len(steps) - 1
    outw = []
    for r_, nm in zip(OUT_REGS, R):
        outw.append(f'{g.reg_facts[r_]}')
    o.append(f'  refine ⟨{g.n_final}, {g.mem_final}, {chain}, ug{last}, frg{last}, ' +
             ', '.join(g.slot_facts[('F', s_)] for s_ in KEEP_SLOTS) + f', {g.slot_facts[("F", 0xF8)]}, ?_, ' +
             f'{g.reg_facts[2]}, {g.reg_facts[3]}.trans hG3.symm, {g.reg_facts[4]}.trans hG4.symm⟩')
    o.append('  rw [' + ', '.join(outw) + ']')
    o.append('  simp only [List.map_cons, List.map_nil]')
    o.append('  rw [' + ', '.join(f'h{nm}' for nm in R) + ']')
    o += ['', 'end C3.RV32']
    open(os.path.join(ROOT, 'C3BootProofs/Proofs/ScalarMontBody.lean'), 'w').write('\n'.join(o) + '\n')
    print(f'{len(lemmas)} value lemmas, {len(g.seg_thms)} segments, '
          f'{sum(1 for v in sp.vals if v[0] not in words)} values inlined')


if __name__ == '__main__':
    main()
