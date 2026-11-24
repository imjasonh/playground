#!/usr/bin/env python3
"""Writes C3BootProofs/Models/PrimeCerts.lean: Pratt certificates for the
curve primes and group orders.

Each certified prime p gets a witness a and the factorization of p - 1, and
every prime in that factorization is certified the same way, down to 2. The
factoring is trial division, Brent's variant of Pollard's rho, and the
elliptic curve method (ECM) on Montgomery curves, with Miller-Rabin to tell
when a cofactor is a probable prime. Probable primality only steers the
search: the kernel checks every certificate.

Usage: python3 scripts/gen-prime-certs.py [--no-hints] > C3BootProofs/Models/PrimeCerts.lean
"""

import math
import random
import sys

TARGETS = [
    ("p256", 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF),
    ("p256_n", 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551),
    (
        "p384",
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFF0000000000000000FFFFFFFF,
    ),
    (
        "p384_n",
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973,
    ),
    ("ed25519_p", 2**255 - 19),
    ("ed25519_L", 2**252 + 27742317777372353535851937790883648493),
]

# Prime factors that this script's ECM takes hours to find. PARI/GP's factor
# found them; a hint is used only where it divides, and --no-hints leaves
# them to ECM. This one divides Ed25519's L - 1.
HINTS = [
    198211423230930754013084525763697,
]

SMALL_PRIMES = [q for q in range(2, 1000) if all(q % d for d in range(2, int(q**0.5) + 1))]


def probable_prime(n):
    if n < 2:
        return False
    for q in SMALL_PRIMES[:20]:
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in SMALL_PRIMES[:20]:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def rho(n, rng, limit):
    """Brent's rho: a nontrivial factor of n, or None after about limit steps."""
    y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
    g = r = q = 1
    x = ys = y
    steps = 0
    while g == 1:
        x = y
        for _ in range(r):
            y = (y * y + c) % n
        k = 0
        while k < r and g == 1:
            ys = y
            for _ in range(min(m, r - k)):
                y = (y * y + c) % n
                q = q * abs(x - y) % n
            g = math.gcd(q, n)
            k += m
        r *= 2
        steps += r
        if steps > limit:
            return None
    if g == n:
        g = 1
        while g == 1:
            ys = (ys * ys + c) % n
            g = math.gcd(abs(x - ys), n)
    return g if g != n else None


def ecm_curve(n, sigma, b1, b2):
    """One ECM curve with Suyama's parametrization: a factor of n, or None."""
    u = (sigma * sigma - 5) % n
    v = 4 * sigma % n
    x0 = pow(u, 3, n)
    z0 = pow(v, 3, n)
    den = 4 * x0 * v % n
    g = math.gcd(den, n)
    if g != 1:
        return g if g != n else None
    a24 = pow(v - u, 3, n) * (3 * u + v) % n * pow(4 * den, -1, n) % n

    def dbl(x, z):
        s, d = (x + z) ** 2 % n, (x - z) ** 2 % n
        t = s - d
        return s * d % n, t * (d + a24 * t) % n

    def add(x1, z1, x2, z2, xd, zd):
        da = (x1 - z1) * (x2 + z2) % n
        cb = (x1 + z1) * (x2 - z2) % n
        return zd * (da + cb) ** 2 % n, xd * (da - cb) ** 2 % n

    def mul(k, x, z):
        r0, r1 = (x, z), dbl(x, z)
        for bit in bin(k)[3:]:
            if bit == "1":
                r0, r1 = add(*r0, *r1, x, z), dbl(*r1)
            else:
                r0, r1 = dbl(*r0), add(*r0, *r1, x, z)
        return r0

    x, z = x0, z0
    for p in primes_upto(b1):
        pk = p
        while pk * p <= b1:
            pk *= p
        x, z = mul(pk, x, z)
    g = math.gcd(z, n)
    if g != 1:
        return g if g != n else None
    # Stage 2: each prime p = m D ± d in (b1, b2] meets the point m D Q at
    # the point d Q.
    step = 2310
    baby = [None, (x, z), dbl(x, z)]
    for k in range(3, step // 2 + 1):
        baby.append(add(*baby[k - 1], x, z, *baby[k - 2]))
    xd, zd = mul(step, x, z)
    m = b1 // step
    prev, cur = mul(m * step, x, z), mul((m + 1) * step, x, z)
    acc = 1
    for ds in stage2_plan(b1, b2, step):
        xr, zr = cur
        for d in ds:
            bx, bz = baby[d]
            acc = acc * (xr * bz - bx * zr) % n
        prev, cur = cur, add(*cur, xd, zd, *prev)
    g = math.gcd(acc, n)
    return g if g not in (1, n) else None


_PLANS = {}


def stage2_plan(b1, b2, step):
    """For each giant step m D from (b1 // D + 1) D, the d with m D ± d prime."""
    key = (b1, b2, step)
    if key not in _PLANS:
        primes = set(primes_between(b1, b2))
        plan = []
        m = b1 // step + 1
        while (m - 1) * step <= b2:
            plan.append([d for d in range(1, step // 2 + 1) if m * step - d in primes or m * step + d in primes])
            m += 1
        _PLANS[key] = plan
    return _PLANS[key]


_SIEVE = []


def primes_upto(b):
    global _SIEVE
    if len(_SIEVE) <= b:
        s = bytearray([1]) * (b + 1)
        s[0:2] = b"\x00\x00"
        for i in range(2, int(b**0.5) + 1):
            if s[i]:
                s[i * i :: i] = bytearray(len(s[i * i :: i]))
        _SIEVE = s
    return [i for i in range(b + 1) if _SIEVE[i]]


def primes_between(lo, hi):
    primes_upto(hi)
    return [i for i in range(lo + 1, hi + 1) if _SIEVE[i]]


def split(n, rng):
    """A nontrivial factor of the composite n."""
    g = rho(n, rng, 1 << 18)
    if g:
        return g
    sigma = 6
    while True:
        g = ecm_curve(n, sigma, 50000, 5000000)
        if g:
            return g
        sigma += 1


def factor(n, hints):
    """The factorization of n as a sorted list of (prime, exponent)."""
    out = {}
    for q in SMALL_PRIMES + hints:
        while n % q == 0:
            out[q] = out.get(q, 0) + 1
            n //= q
    rng = random.Random(n)
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if probable_prime(m):
            out[m] = out.get(m, 0) + 1
            continue
        d = split(m, rng)
        stack += [d, m // d]
    return sorted(out.items())


def witness(p, fs):
    """The least a that passes Lucas's test for p with factors fs."""
    if p == 2:
        return 1
    for a in range(2, p):
        if pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // q, p) != 1 for q, _ in fs):
            return a
    raise ValueError(f"{p} is not prime")


def main():
    hints = [] if "--no-hints" in sys.argv[1:] else HINTS
    certs = {}

    def certify(p):
        if p in certs:
            return
        fs = factor(p - 1, hints)
        for q, _ in fs:
            certify(q)
        certs[p] = (witness(p, fs), fs)

    for _, p in TARGETS:
        certify(p)

    names = {p: name for name, p in TARGETS}
    for p in certs:
        names.setdefault(p, f"q{p}" if p < 10**12 else f"q{p.bit_length()}_{p % 10**6:06d}")
    assert len(set(names.values())) == len(names)

    out = sys.stdout
    out.write("import C3BootProofs.Models.PrimeLucas\n\n")
    out.write("/-!\n# Pratt certificates for the curve primes\n\n")
    out.write("Generated by `scripts/gen-prime-certs.py`; do not edit. Each prime has a\n")
    out.write("witness and the factorization of `p - 1`, whose primes are certified\n")
    out.write("before it. The kernel evaluates `checkLucas` on each.\n-/\n\n")
    out.write("namespace C3.Models.PrimeCerts\n\n")
    # certs is filled in post-order: every factor precedes the prime it divides.
    for p, (a, fs) in certs.items():
        n = names[p]
        flist = ", ".join(f"({q}, {e})" for q, e in fs)
        proofs = "".join(f"⟨prime_{names[q]}, " for q, _ in fs) + "trivial" + "⟩" * len(fs)
        out.write(f"theorem prime_{n} : IsPrime {p} :=\n")
        out.write(f"  isPrime_of_checkLucas {p} {a}\n    [{flist}]\n")
        out.write(f"    (by decide +kernel)\n    {proofs}\n\n")
    out.write("end C3.Models.PrimeCerts\n")
    print(f"{len(certs)} certificates", file=sys.stderr)


if __name__ == "__main__":
    main()
