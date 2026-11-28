#!/usr/bin/env python3
"""Computes cofactors for `ring_mod`'s hypotheses and prints them as Lean.

`ring_mod [h₁ * c₁, …, hₖ * cₖ]` proves `a % n = b % n` from hypotheses
`hᵢ : Eᵢ % n = 0` when `a - b - (E₁ * c₁ + … + Eₖ * cₖ)` has every
coefficient a multiple of `n`. This script finds the `cᵢ` by multivariate
division of `a - b` by the `Eᵢ`, with coefficients modulo `n`, in the graded
reverse lexicographic order of the variables as listed. The remainder has
to be zero. It is whenever `a - b` is in the ideal of the `Eᵢ` and they
form a Gröbner basis, as curve equations in disjoint variables do.

Expressions use `+`, `-`, `*`, `^` or `**` with a numeral exponent,
parentheses, numerals (decimal or `0x` hexadecimal), variables, and names
that `--let` defines. `--let` definitions are expanded, so the cofactors
mention only variables.

Example, for two points on y^2 = x^3 + 7 modulo 101:

    ring-cofactors.py --mod 101 --vars x1=x₁,y1=y₁,x2=x₂,y2=y₂ \\
        --lhs 'y1^2 * y2^2' --rhs '(x1^3 + 7) * (x2^3 + 7)' \\
        --hyp 'y1^2 - x1^3 - 7' --hyp 'y2^2 - x2^3 - 7' --names h₁,h₂

prints `ring_mod [h₁ * (…), h₂ * (…)]`. Without `--names`, it prints one
cofactor per line. Powers print as `x ^ (2 : Nat)`: Lean elaborates a term
with many `x ^ 2` slowly, because it resolves each exponent's type by
default instances, and the ascription skips that.

Pass an expression that starts with `-` as `--hyp=EXPR` or `--lhs=EXPR`,
so that it isn't read as an option.

Usage: ring-cofactors.py --mod N --vars V[=LEAN],... [--let NAME=EXPR]...
    --lhs EXPR [--rhs EXPR] --hyp EXPR... [--names H,...]
"""

import argparse
import ast
import sys


class Ring:
  """Polynomials as dicts from exponent tuples to coefficients modulo n."""

  def __init__(self, n, nvars):
    self.n = n
    self.nvars = nvars

  def red(self, c):
    return c % self.n if self.n else c

  def norm(self, p):
    out = {}
    for m, c in p.items():
      c = self.red(c)
      if c:
        out[m] = c
    return out

  def const(self, c):
    return self.norm({(0,) * self.nvars: c})

  def var(self, i):
    m = [0] * self.nvars
    m[i] = 1
    return {tuple(m): 1}

  def add(self, p, q):
    out = dict(p)
    for m, c in q.items():
      out[m] = out.get(m, 0) + c
    return self.norm(out)

  def scale(self, p, c):
    return self.norm({m: c * d for m, d in p.items()})

  def mul(self, p, q):
    out = {}
    for m1, c1 in p.items():
      for m2, c2 in q.items():
        m = tuple(a + b for a, b in zip(m1, m2))
        out[m] = out.get(m, 0) + c1 * c2
    return self.norm(out)

  def pow(self, p, k):
    out = self.const(1)
    for _ in range(k):
      out = self.mul(out, p)
    return out

  def inverse(self, c):
    if self.n:
      return pow(c, -1, self.n)
    if c in (1, -1):
      return c
    raise ValueError(f'leading coefficient {c} has no inverse over the integers')


def order_key(m):
  """Graded reverse lexicographic order: a larger key is a larger monomial."""
  return (sum(m), tuple(-e for e in reversed(m)))


def leading(p):
  m = max(p, key=order_key)
  return m, p[m]


def divides(a, b):
  return all(x <= y for x, y in zip(a, b))


def divide(ring, f, divisors):
  """Returns the quotients and the remainder of f by the divisors."""
  quotients = [{} for _ in divisors]
  leads = [leading(g) for g in divisors]
  rem = {}
  f = dict(f)
  while f:
    m, c = leading(f)
    for i, (gm, gc) in enumerate(leads):
      if divides(gm, m):
        qm = tuple(a - b for a, b in zip(m, gm))
        qc = ring.red(c * ring.inverse(gc))
        term = {qm: qc}
        quotients[i] = ring.add(quotients[i], term)
        f = ring.add(f, ring.scale(ring.mul(term, divisors[i]), -1))
        break
    else:
      rem = ring.add(rem, {m: c})
      f = ring.add(f, {m: -c})
  return quotients, rem


def parse(ring, src, names):
  """Parses an expression into a polynomial."""
  tree = ast.parse(src.replace('^', '**'), mode='eval')

  def ev(node):
    if isinstance(node, ast.Expression):
      return ev(node.body)
    if isinstance(node, ast.BinOp):
      if isinstance(node.op, ast.Pow):
        exp = node.right.value if isinstance(node.right, ast.Constant) else None
        if not isinstance(exp, int) or exp < 0:
          raise ValueError('exponents must be numerals')
        return ring.pow(ev(node.left), exp)
      a, b = ev(node.left), ev(node.right)
      if isinstance(node.op, ast.Add):
        return ring.add(a, b)
      if isinstance(node.op, ast.Sub):
        return ring.add(a, ring.scale(b, -1))
      if isinstance(node.op, ast.Mult):
        return ring.mul(a, b)
    if isinstance(node, ast.UnaryOp):
      if isinstance(node.op, ast.USub):
        return ring.scale(ev(node.operand), -1)
      if isinstance(node.op, ast.UAdd):
        return ev(node.operand)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
      return ring.const(node.value)
    if isinstance(node, ast.Name):
      if node.id not in names:
        raise ValueError(f'unknown name {node.id}')
      return names[node.id]
    raise ValueError(f'unsupported expression: {ast.dump(node)}')

  return ev(tree)


def to_lean(ring, p, lean_vars):
  """Prints a polynomial as a Lean term, largest monomial first."""
  if not p:
    return '0'
  parts = []
  for m in sorted(p, key=order_key, reverse=True):
    c = p[m]
    if ring.n and c > ring.n // 2:
      c -= ring.n
    factors = []
    for v, e in zip(lean_vars, m):
      if e == 1:
        factors.append(v)
      elif e > 1:
        factors.append(f'{v} ^ ({e} : Nat)')
    if abs(c) != 1 or not factors:
      factors.insert(0, str(abs(c)))
    term = ' * '.join(factors)
    if not parts:
      parts.append(f'-{term}' if c < 0 else term)
    else:
      parts.append(f'- {term}' if c < 0 else f'+ {term}')
  return ' '.join(parts)


def main():
  ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
  ap.add_argument('--mod', required=True, help='the modulus, or 0 for exact integers')
  ap.add_argument('--vars', required=True, help='variables, as NAME or NAME=LEAN')
  ap.add_argument('--let', action='append', default=[], dest='lets', help='NAME=EXPR')
  ap.add_argument('--lhs', required=True)
  ap.add_argument('--rhs', default='0')
  ap.add_argument('--hyp', action='append', default=[], help="a hypothesis's E")
  ap.add_argument('--names', help="the hypotheses' Lean names, comma-separated")
  args = ap.parse_args()

  specs = [v.strip() for v in args.vars.split(',') if v.strip()]
  py_vars = [s.split('=', 1)[0] for s in specs]
  lean_vars = [s.split('=', 1)[1] if '=' in s else s for s in specs]
  n = parse(Ring(0, 0), args.mod, {}).get((), 0)
  ring = Ring(n, len(py_vars))
  names = {v: ring.var(i) for i, v in enumerate(py_vars)}
  for d in args.lets:
    name, expr = d.split('=', 1)
    names[name.strip()] = parse(ring, expr, names)

  f = ring.add(parse(ring, args.lhs, names),
               ring.scale(parse(ring, args.rhs, names), -1))
  hyps = [parse(ring, h, names) for h in args.hyp]
  if any(not h for h in hyps):
    sys.exit('a hypothesis is zero modulo the modulus')
  quotients, rem = divide(ring, f, hyps)
  if rem and not hyps:
    sys.exit('the sides differ by:\n  ' + to_lean(ring, rem, lean_vars))
  if rem:
    sys.exit('the remainder is not zero, so the identity does not follow from '
             'these hypotheses by division:\n  ' + to_lean(ring, rem, lean_vars))

  cofactors = [to_lean(ring, q, lean_vars) for q in quotients]
  if args.names:
    hnames = [h.strip() for h in args.names.split(',')]
    if len(hnames) != len(cofactors):
      sys.exit('--names needs one name for each --hyp')
    pairs = ', '.join(f'{h} * ({c})' for h, c in zip(hnames, cofactors))
    print(f'ring_mod [{pairs}]')
  else:
    for c in cofactors:
      print(c)


if __name__ == '__main__':
  main()
