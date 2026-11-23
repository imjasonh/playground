#!/usr/bin/env python3
"""Writes `SvVerifyAt.lean`: `sv_verify` for a `Bundle` and a `SigstoreRoot`.

`sv_verify` states what it needs of the bundle at `a1` and the trust root at
`a2` as words and slices at offsets from them. `sv_verify_at` takes instead
that a `Bundle` and a `SigstoreRoot` lie there (`SvBundleAt`, `SvRootAt`) and
derives each of those hypotheses. The rest stay hypotheses: where the code
and constants are, the stack's place, the output and digest buffers, and the
P-256 and P-384 inversions' side conditions.

Usage: python3 scripts/gen-sv-layout.py   (from c3-boot-proofs/)
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from svchain import groups, strip_parens, top_split  # noqa: E402

SRC = 'C3BootProofs/Proofs/SvVerify.lean'
ROOT, BUN = "reg n a2", "reg n a1"
POLICY = {0x0: 'issuer', 0x8: 'buildSignerUri', 0x10: 'repositoryId', 0x18: 'ownerId', 0x20: 'trigger'}
FIELDS = {0x0: 'leaf', 0x8: 'imageSignature', 0x10: 'inclusionProof', 0x18: 'checkpoint', 0x20: 'timestamp'}
# A search's start pointer from the root: the array it walks, that array's
# offset, and where an entry starts from the search's pointer.
ARRAYS = {0x3C: ('fulcio', 0x38, -4), 0x98: ('logs', 0xB8, 0x20), 0x198: ('tsas', 0x1B8, 0x20)}
EQ = "(by rw [hy]; bv_omega)"


def offset(expr, base):
    """`expr` as `base` plus a constant, or None."""
    e = expr.replace('(', ' ').replace(')', ' ')
    if not re.search(rf"(?<![\w.']){re.escape(base)}(?![\w'])", e):
        return None
    e = re.sub(rf"(?<![\w.']){re.escape(base)}(?![\w'])", " ", e, count=1)
    e = re.sub(r"BitVec\.ofNat 32", " ", e)
    toks = e.split()
    if any(t not in ('+',) and not re.fullmatch(r"0x[0-9A-Fa-f]+|\d+", t) for t in toks):
        return None
    total = sum(int(t, 0) for t in toks if t != '+') % 2 ** 32
    return total - 2 ** 32 if total >= 2 ** 31 else total


def unwrap(x):
    while True:
        y = strip_parens(x.strip())
        if y == x:
            return y
        x = y


def slice_of(t):
    """`SvIn B (memLoad32 Me (a)) (memLoad32 Me (b)).toNat`, or `SvRo`, as (kind, a, b)."""
    toks = top_split(t, ' ')
    if len(toks) != 4 or toks[0] not in ('SvIn', 'SvRo') or toks[1] != 'B' or not toks[3].endswith('.toNat'):
        return None
    ptr, ln = unwrap(toks[2]), unwrap(toks[3][:-len('.toNat')])
    mp = re.fullmatch(r"memLoad32 Me \((.+)\)", ptr)
    ml = re.fullmatch(r"memLoad32 Me \((.+)\)", ln)
    return (toks[0], mp.group(1), ml.group(1)) if mp and ml else None


def plain(p, t):
    """A proof of hypothesis `t` that names no search state, or None."""
    t = strip_parens(t)
    if p == 'hb':
        return "Bd.al"
    if p == 'sb':
        return "Bd.sep"
    m = re.fullmatch(r"SvIn B (.+) 4", t) or re.fullmatch(r"\((.+)\)\.toNat % 4 = 0", t)
    if m:
        part = ".1" if t.startswith("SvIn") else ".2"
        for base, h in ((ROOT, "R"), (BUN, "Bd")):
            c = offset(m.group(1), base)
            if c is not None and c >= 0:
                return f"({h}.inn.wordAt {h}.al (c := 0x{c:X}) (by decide) (by decide) (by bv_omega)){part}"
    sl = slice_of(t)
    if sl:
        kind, a, b = sl
        ca, cb = offset(a, ROOT), offset(b, ROOT)
        if kind == "SvRo" and ca in POLICY and cb == ca + 4:
            return f"(R.{POLICY[ca]}.1.load2 (by bv_omega) (by bv_omega))"
        ca, cb = offset(a, BUN), offset(b, BUN)
        if kind == "SvIn" and ca in FIELDS and cb == ca + 4:
            return f"(Bd.{FIELDS[ca]}.1.load2 (by bv_omega) (by bv_omega))"
    return None


def entry_part(t, q, base_q, arr, listed):
    """A proof of one fact about a search's entry, or None. `listed` is the
    tactic that gets the entry's `SvEntryAt` as `E`."""
    t = strip_parens(t)
    m = re.fullmatch(r"\(?memLoad32 Me \((.+?)\)\)? ≠ 0 → (.+)", t)
    if m:
        inner = entry_part(m.group(2), q, base_q, arr, None)
        if inner is None:
            return None
        return f"(by intro g; {listing(m.group(1), q, arr)}; exact {inner})"
    m = re.fullmatch(r"SvIn B (.+) 4", t) or re.fullmatch(r"\((.+)\)\.toNat % 4 = 0", t)
    if m and not m.group(1).startswith("(memLoad32") and not m.group(1).startswith("memLoad32"):
        c = offset(m.group(1), q)
        if c is not None:
            part = ".1" if t.startswith("SvIn") else ".2"
            return (f"(R.inn.wordAt R.al (c := 0x{base_q + c:X} + 0x20 * i) (by omega) (by omega) {EQ}){part}")
    m = re.fullmatch(r"SvIn B (.+) (\d+)", t)
    if m and not m.group(1).lstrip('(').startswith("memLoad32"):
        c = offset(m.group(1), q)
        if c is not None:
            return f"((R.inn.sub (c := 0x{base_q + c:X} + 0x20 * i) (l := {m.group(2)}) (by omega)).ptr {EQ})"
    m = re.fullmatch(r"SvIn B \(?memLoad32 Me \((.+?)\)\)? (0x[0-9A-F]+|\d+)", t)
    if m and offset(m.group(1), q) is not None:
        return f"(E.keyIn.load {EQ})"
    m = re.fullmatch(r"SvIn B \(?memLoad32 Me \((.+?)\)\)? \(?\(memLoad32 Me \((.+)\)\)\)?\.toNat", t)
    if m and offset(m.group(1), q) is not None:
        return f"(E.name.1.load2 {EQ} {EQ})"
    return None


def listing(addr, q, arr):
    name, a_off, _ = arr
    return (f"obtain ⟨_, E⟩ := R.{name}.listed hi (by rw [show {ROOT} + 0x{a_off:X} + BitVec.ofNat 32 (0x20 * i) = "
            f"{addr} by rw [hy]; bv_omega]; exact g)")


def quantified(t):
    arrows = top_split(t, ' → ')
    if len(arrows) < 3 or not re.fullmatch(r"∀ i, i < \d+", arrows[0]):
        return None
    m = re.fullmatch(r"∀ ([\w' ]+), \(([\w', ]+)\) = svIter (.+) i (\(.+\))", arrows[1])
    if not m:
        return None
    vs = m.group(1).split()
    init = [strip_parens(x) for x in top_split(strip_parens(m.group(4)), ', ')]
    if len(init) < 2:
        return None
    base_q = offset(init[1], ROOT)
    if base_q not in ARRAYS:
        return None
    arr = ARRAYS[base_q]
    q = vs[1]
    rest = " → ".join(arrows[2:])
    guard = None
    gm = re.fullmatch(r"\(?memLoad32 Me \((.+?)\)\)? ≠ 0", strip_parens(arrows[2]))
    if gm and len(arrows) > 3 and offset(gm.group(1), q) is not None:
        guard, rest = gm.group(1), " → ".join(arrows[3:])
    parts = [x.strip() for x in top_split(strip_parens(rest), ' ∧ ')]
    proofs = [entry_part(x, q, base_q, arr, guard) for x in parts]
    if any(p is None for p in proofs):
        return None
    lem = "svIter_ptr2" if len(vs) == 2 else "svIter_ptr3"
    body = proofs[0] if len(proofs) == 1 else "⟨" + ", ".join(proofs) + "⟩"
    pre = f"intro g; {listing(guard, q, arr)}; " if guard else ""
    return f"(fun i hi {' '.join(vs)} h => by have hy := {lem} h; {pre}exact {body})"


def main():
    src = open(SRC).read()
    i = src.index('theorem sv_verify ')
    stmt = src[i:src.index(':= by\n', i)]
    header = stmt.split('\n', 1)[0][len('theorem sv_verify '):]
    k0 = stmt.index('(C : ')
    k1 = stmt.index('\n    SvErrRet')
    hyps = [tuple(x.strip() for x in g.split(' : ', 1)) for g in groups(stmt[k0:k1])]
    concl = stmt[k1 + 1:]
    derived, kept, seen = {}, [], {}
    for p, t in hyps:
        tt = re.sub(r"\s+", " ", t)
        pf = plain(p, tt) or quantified(tt)
        if pf:
            derived[p] = pf
        elif tt in seen:
            derived[p] = seen[tt]
        else:
            seen[tt] = p
            kept.append((p, t))

    out = []
    O = out.append
    O("import C3BootProofs.Proofs.SvLayout")
    O("")
    O("/-!\n# `sigstore::verify` for a `Bundle` and a `SigstoreRoot`\n\nWritten by `scripts/gen-sv-layout.py` "
      "from `sv_verify`.\n-/")
    O("")
    O("namespace C3.RV32.Sv")
    O("")
    for line in src.split('\n'):
        if line.startswith('open '):
            O(line)
            O("")
            break
    O("set_option maxHeartbeats 64000000 in")
    O("set_option maxRecDepth 100000 in")
    O("/-- **`sigstore::verify` for a `Bundle` and a `SigstoreRoot`**: `sv_verify`, with the bundle at `a1` "
      "and the trust root at `a2` laid out as `SvBundleAt` and `SvRootAt` say. -/")
    O(f"theorem sv_verify_at {header} {{bundle : Bundle}} {{root : SigstoreRoot}}")
    O("    (Bd : SvBundleAt B Me (reg n a1) bundle) (R : SvRootAt B Me (reg n a2) root)")
    O("\n".join(f"    ({p} : {t})" for p, t in kept) + " :")
    O(concl + ":= by")
    O("  exact sv_verify " + " ".join(derived.get(p, p) for p, _ in hyps))
    O("")
    O("end C3.RV32.Sv")
    O("")
    open('C3BootProofs/Proofs/SvVerifyAt.lean', 'w').write("\n".join(out))
    print(f"derived {len(derived)}, kept {len(kept)}: {' '.join(p for p, _ in kept)}")


if __name__ == "__main__":
    main()
