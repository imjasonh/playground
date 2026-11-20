#!/usr/bin/env python3
"""Writes the stages of the `sigstore::verify` proof.

A stage is a list of operations on the machine: blocks of ALU instructions,
loads and stores on the frame, `memcpy` within the frame, and calls through
the wrappers in `SvDer.lean`. The script follows the registers and the
frame's words and bytes through the operations and writes a Lean proof with
one `have` per fact per step. A call that can fail splits the proof: the
failing case runs to the error exit at 0x966, and the stage's conclusion
says the checks failed and the function returned `Err`; the other case goes
on.

Usage: python3 scripts/gen-sigstore-verify.py STAGE > C3BootProofs/Proofs/Sv<STAGE>.lean
"""

import os
import re
import sys

AT = open("C3BootProofs/Proofs/SvAt.lean").read()
INSTR = {}
for mm in re.finditer(
    r"theorem sv_at_([0-9a-f]+) : fetchRel sigstoreVerifyCode 0x[0-9A-F]+ = some \((.*), (\d+)\) :=", AT
):
    INSTR[int(mm.group(1), 16)] = (mm.group(2), int(mm.group(3)))

REGS = {"x0": 0, "ra": 1, "sp": 2, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17,
        "t0": 5, "t1": 6}
# Registers a call through `oidKeep` keeps.
OID_KEEP = [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
# Registers every callee keeps.
CALL_KEEP = [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
FRAME = 0x1690
SAVES = 0x165C
MCS_OFF = None


def reg_of(tok):
    if tok in REGS:
        return REGS[tok]
    mm = re.fullmatch(r"\((\d+) : Fin 32\)", tok)
    if mm:
        return int(mm.group(1))
    raise ValueError(tok)


def rname(r):
    for k, v in REGS.items():
        if v == r and k not in ("x0", "ra", "t0", "t1"):
            return k
    return f"({r} : Fin 32)"


def tokens(s):
    return re.findall(r"\(\d+ : Fin 32\)|\S+", s)


def s32(v):
    v &= 0xFFFFFFFF
    return v - (1 << 32) if v & 0x80000000 else v


def add(a, b):
    if a is None or b is None:
        return None
    if a[0] == "C" and b[0] == "C":
        return ("C", (a[1] + b[1]) & 0xFFFFFFFF)
    if a[0] == "S" and b[0] == "C":
        return ("S", (a[1] + s32(b[1])) & 0xFFFFFFFF)
    if a[0] == "C" and b[0] == "S":
        return add(b, a)
    if a[0] == "C" and a[1] == 0:
        return b
    if b[0] == "C" and b[1] == 0:
        return a
    if a[0] == "U" and b[0] == "C":
        return ("U", f"({a[1]}) + BitVec.ofNat 32 0x{b[1] & 0xFFFFFFFF:X}")
    if a[0] == "U" and b[0] == "U":
        return ("U", f"({a[1]}) + ({b[1]})")
    return None


def outside(kind, e, n):
    """Whether the `n` bytes at offset `e` are apart from what a step that `kind`
    describes wrote."""
    if kind[0] == "same":
        return True
    if kind[0] == "K":
        c, w = kind[1], kind[2]
        return e + n <= c or c + w <= e
    return all(e + n <= c or c + w <= e for c, w in kind[1])


def fa(e):
    """The address of offset `e` of the frame."""
    return "B + 0x21A0" if e == 0 else f"B + 0x21A0 + BitVec.ofNat 32 0x{e:X}"


def lean_val(v):
    if isinstance(v, str):
        return v
    if v[0] == "S":
        return fa(v[1])
    if v[0] == "C":
        return f"BitVec.ofNat 32 0x{v[1]:X}"
    return v[1]


def nat_of(w):
    """`n` from the word `BitVec.ofNat 32 n`."""
    assert w.startswith("BitVec.ofNat 32 "), w
    n = w[len("BitVec.ofNat 32 "):]
    return n[1:-1] if n.startswith("(") and n.endswith(")") else n


def rt_fail(sub, k, oc, dc, fail_tail):
    """`read_time`'s failing case: 1 at `oc`, then `fail_tail`."""
    sub.emit(f"  have y0_{k} := Er{k} hr{k}")
    sub.frame_after(k, [(oc, 16), (dc + 8, 8)], {}, {oc: ("(1 : BitVec 8)", f"y0_{k}")})
    fail_tail(sub)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")))


def seq_fail(sub, k, oc, dc, lw_off, lbu_off, br_off):
    """`Der::sequence`'s failing case: the null address, then `lw`, `lbu`, and `beqz` to 0x966."""
    sub.emit(f"  obtain ⟨z{k}, -⟩ := Er{k} er{k} hr{k}")
    sub.frame_after(k, [(oc, 16), (dc + 8, 8)], {oc: ("0", f"z{k}")})
    sub.load(lw_off, "lw")
    sub.load_any(lbu_off)
    reg = reg_of(tokens(INSTR[br_off][0])[2])
    sub.branch(br_off, True, f"by rw [g{sub.k}_{reg}, s{sub.k}.zero]; rfl")
    sub.fail(sub.fail_proof(("eq", f"hr{k}")))


def es_fail(sub, k, off, oc):
    """`der::ecdsa_signature`'s failing case: 1 at `oc`, then `lbu`, `lbu`, `bnez`."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
    sub.frame_after(k, [(oc, 97)], {}, {oc: ("(1 : BitVec 8)", f"y0_{k}")})
    sub.load(off + 8, "lbu")
    sub.load_any(off + 0xC)
    sub.branch(off + 0x10, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.fail(sub.fail_proof(("eq", f"hr{k}")))


def oid_fail(sub, k, oc, dc, fail_tail, exit_lemma="sv_fail"):
    """`Der::oid`'s failing case: the null address at `oc`, then `fail_tail`."""
    sub.emit(f"  obtain ⟨z{k}, -⟩ := Er{k} er{k} hr{k}")
    sub.frame_after(k, [(oc, 8), (dc + 8, 8)], {oc: ("0", f"z{k}")})
    fail_tail(sub)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), exit_lemma)


def ds32_fail(sub, k, oc, dc, fail_tail):
    """`der::scalar::<32>`'s failing case: 1 and the error byte at `oc`, then `fail_tail`."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, y1_{k}⟩ := R{k}")
    sub.frame_after(k, [(oc, 33), (dc + 8, 8)], {},
                    {oc: ("(1 : BitVec 8)", f"y0_{k}"), oc + 1: (f"eb{k}", f"y1_{k}")})
    fail_tail(sub)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def es2_fail(sub, k, off, oc):
    """`der::ecdsa_signature`'s failing case at a `beqz` site: 1 at `oc`, `lbu`,
    `lbu`, `beqz` not taken, `mv s0, s9`, and `j` to 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
    sub.frame_after(k, [(oc, 97)], {}, {oc: ("(1 : BitVec 8)", f"y0_{k}")})
    sub.load(off + 8, "lbu")
    sub.load_any(off + 0xC)
    sub.branch(off + 0x10, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.block(off + 0x12, off + 0x14)
    sub.jump(off + 0x14)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def err44(sub, entry):
    """The failing exits that go through 0xB46, from `entry`."""
    if entry == 0xB3C:
        sub.load_any(0xB3C)
        sub.jump(0xB40)
        entry = 0xB44
    if entry == 0xB42:
        sub.block(0xB42, 0xB44)
        entry = 0xB44
    if entry == 0xB44:
        sub.store(0xB44, "sw")
    if entry == 0xB2E:
        sub.block(0xB2E, 0xB30)
        sub.jump(0xB30)
        entry = 0xB38
    if entry == 0xB36:
        sub.block(0xB36, 0xB38)
        entry = 0xB38
    if entry == 0x9BA:
        sub.load_any(0x9BA)
        sub.jump(0x9BE)
        entry = 0xB38
    if entry == 0xB38:
        sub.store(0xB38, "sw")
        sub.jump(0xB3A)
    sub.load_any(0xB46, "lw")
    sub.jump(0xB48)


def fail_elem(sub, k, oc, dc, hr, null, width, fail_tail, exit_lemma="sv_fail"):
    """A reader's failing case: the null address at `oc`, then `fail_tail`."""
    sub.emit(f"  obtain ⟨z{hr}, -⟩ := {null}")
    sub.frame_after(k, [(oc, width), (dc + 8, 8)], {oc: ("0", f"z{hr}")})
    fail_tail(sub)
    sub.fail(sub.fail_proof(("eq", hr)), exit_lemma)


class Gen:
    def __init__(self, name):
        self.name = name
        self.k = 0
        self.out = []
        self.blocks = []
        self.regs = {}
        self.words = {}
        self.bytes = {}
        self.depth = 0  # how many failing cases the proof has closed
        self.fails = []  # the failing cases, each a Lean Prop over the stage's witnesses
        self.wit = []  # (binder, Prop) witnesses of the successful checks
        self.ind = "  "
        self.sc = []  # the checks so far: ("eq", expr, pattern, binders, hr) or ("prop", P, h)
        self.slices = {}  # (address, length word) of bytes outside the stack -> a proof of `SvIn`
        self.slices_nat = {}  # (address, length) -> a proof of `SvIn`
        self.pinned = set()  # names `end_step` keeps
        self.extra = []  # (conjunct, term) pairs the conclusion adds
        self.generic_alu = False  # single ALU instructions the evaluator lacks become `aluEval` terms
        self.digest = None  # (step, offset, value) of a SHA-256 digest in the frame
        self.hasher = None  # (step, message, length facts) of the SHA-256 hasher at 0x420
        self.ranges = {}  # frame offset -> (length, the byte at offset + j, in terms of `j`)
        self.acc = {}  # frame offset -> (limbs, the value of `accV` there)
        self.exits = []  # forks that reach the stage's end: (placeholder, generator)

    def emit(self, s):
        self.out.append(self.ind + s[2:] if s.startswith("  ") else s)

    def clone(self):
        c = Gen(self.name)
        for kk, vv in self.__dict__.items():
            c.__dict__[kk] = vv if kk in ("blocks", "exits") else dict(vv) if isinstance(vv, dict) else list(vv) if isinstance(vv, list) else vv
        c.out = []
        c.mark = 0
        c.prev_lines = self.out[getattr(self, "prev_mark", 0):]
        c.prev_mark = 0
        return c

    def fork(self, fail):
        """Runs `fail` on a copy of the generator, indented as the first case of a
        split, and appends its lines."""
        sub = self.clone()
        sub.ind = self.ind + "  "
        fail(sub)
        lines = sub.out
        lines[0] = self.ind + "· " + lines[0][len(sub.ind):]
        self.out += lines

    def end_step(self):
        start = getattr(self, "mark", 0)
        names = []
        for line in self.out[start:]:
            line = line[len(self.ind) - 2:] if line.startswith(self.ind) else line
            mm = re.match(r"  have (\w+)", line)
            if mm:
                names.append(mm.group(1))
            mm = re.match(r"  obtain ⟨([^⟩]*)⟩", line)
            if mm:
                names += [x.strip() for x in mm.group(1).split(",") if not re.fullmatch(r"n\d+", x.strip())]
        keep = {b for c in self.sc if c[0] == "eq" for b in c[3] + [c[4]]} | {c[2] for c in self.sc if c[0] == "prop"}
        keep |= self.pinned
        names = [x for x in names if x not in keep and re.fullmatch(r"[A-Za-z_][\w']*", x) and not x.startswith("keep_")
                 and not x.startswith("ht_") and not x.startswith("hz_") and not x.startswith("hr") and not re.fullmatch(r"r\d+b?", x)]
        prev = getattr(self, "prev_names", [])
        consumed = set()
        for line in getattr(self, "prev_lines", []) + self.out[getattr(self, "prev_mark", 0):]:
            mm = re.search(r"obtain ⟨[^⟩]*⟩ := (\w+)\s*$", line)
            if mm:
                consumed.add(mm.group(1))
        prev = [x for x in prev if x not in consumed]
        self.prev_mark = start
        self.prev_lines = []
        if prev:
            self.out.append(self.ind + "clear " + " ".join(reversed(prev)))
        self.prev_names = names
        self.mark = len(self.out)

    def common(self, k, steps, fr, saves):
        self.emit(f"  have t{k} : Steps n0 n{k} := t{k-1}.trans {steps}")
        self.emit(f"  have fR{k} : ∀ x, SvR B x → n{k}.mem x = M0 x := fun x hx => ({fr} x hx).trans (fR{k-1} x hx)")
        self.emit(f"  have E{k} : SvCode n{k}.mem := E{k-1}.fr F {fr}")
        self.emit(f"  have V{k} : SvSaves B n{k}.mem v := {saves}")

    def word_stmt(self, k, e, v):
        return f"memLoad32 n{k}.mem ({fa(e)}) = {lean_val(v)}"

    def byte_stmt(self, k, e, v):
        return f"n{k}.mem ({fa(e)}) = {v}"

    def keep_frame(self, k, kind, written_words=None, written_bytes=None):
        """Frame facts after step k. `kind` is ("same",) when memory did not change,
        ("K", c, w) for an `SvKeep`, or ("L", ranges) for an `SvKeepL`."""
        written_words = written_words or {}
        written_bytes = written_bytes or {}
        neww, newb = {}, {}

        for e, v in sorted(self.words.items()):
            if e in written_words or not outside(kind, e, 4):
                continue
            if kind[0] == "same":
                pf = f"by rw [m{k}]; exact w{k-1}_{e:x}"
            else:
                pf = f"(K{k}.w32 (by decide) (by decide)).trans w{k-1}_{e:x}"
            self.emit(f"  have w{k}_{e:x} : {self.word_stmt(k, e, v)} := {pf}")
            neww[e] = v
        for e, v in sorted(self.bytes.items()):
            if e in written_bytes or not outside(kind, e, 1):
                continue
            if kind[0] == "same":
                pf = f"by rw [m{k}]; exact b{k-1}_{e:x}"
            else:
                pf = f"(K{k}.b8 (by decide) (by decide)).trans b{k-1}_{e:x}"
            self.emit(f"  have b{k}_{e:x} : {self.byte_stmt(k, e, v)} := {pf}")
            newb[e] = v
        for e, (v, pf) in sorted(written_words.items()):
            self.emit(f"  have w{k}_{e:x} : {self.word_stmt(k, e, v)} := {pf}")
            neww[e] = v
        for e, (v, pf) in sorted(written_bytes.items()):
            self.emit(f"  have b{k}_{e:x} : {self.byte_stmt(k, e, v)} := {pf}")
            newb[e] = v
        newr = {}
        for s, (n, tmpl) in sorted(self.ranges.items()):
            if not outside(kind, s, n):
                continue
            stmt = f"∀ j, j < {n} → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{s:X} + j)) = {tmpl}"
            if kind[0] == "same":
                pf = f"fun j hj => by rw [m{k}]; exact q{k-1}_{s:x} j hj"
            else:
                pf = f"fun j hj => (K{k}.range (by decide) (by decide) j hj).trans (q{k-1}_{s:x} j hj)"
            self.emit(f"  have q{k}_{s:x} : {stmt} := {pf}")
            newr[s] = (n, tmpl)
        newa = {}
        for d, (n, v) in sorted(self.acc.items()):
            if not outside(kind, d, 4 * n):
                continue
            if kind[0] == "same":
                pf = f"by rw [m{k}]; exact a{k-1}_{d:x}"
            else:
                pf = f"(K{k}.acc (by decide) (by decide)).trans a{k-1}_{d:x}"
            self.emit(f"  have a{k}_{d:x} : {self.acc_stmt(k, d, n, v)} := {pf}")
            newa[d] = (n, v)
        self.words, self.bytes, self.ranges, self.acc = neww, newb, newr, newa

    def acc_stmt(self, k, d, n, v):
        return f"accV n{k}.mem ({fa(d)}) {n} = {v}"

    def keep_frame_L(self, k, ranges):
        self.keep_frame(k, ("L", ranges))

    def load_any(self, off, kind="lbu"):
        """`lbu` or `lw` whose value no later step needs."""
        text, ln = INSTR[off]
        tk = tokens(text)
        rd = reg_of(tk[2])
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: {kind}")
        if kind == "lw":
            base, imm = reg_of(tk[3]), int(tk[4], 16)
            bv = self.regs[base]
            e = (bv[1] + s32(imm)) & 0xFFFFFFFF
            self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.lw E{k-1}.self sv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
            self.emit(f"    (by rw [g{k-1}_{base}, show {lean_val(bv)} + 0x{imm:X} = {fa(e)} by sv_addr]; exact sv_al F (by decide) (by decide))")
        else:
            self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.lbu E{k-1}.self sv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
        self.st(k, off + ln)
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"(.single d{k})", f"fr{k}", f"V{k-1}.same m{k}")
        new = {}
        for r, v in sorted(self.regs.items()):
            if r == rd:
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [u{k}.regs, upd_ne (by decide) (by decide), g{k-1}_{r}]")
            new[r] = v
        self.regs = new
        self.keep_frame(k, ("same",))
        self.end_step()

    def keep_regs(self, k, keep, how):
        new = {}
        for r, v in sorted(self.regs.items()):
            if r not in keep:
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [{how(r)}, g{k-1}_{r}]")
            new[r] = v
        self.regs = new

    def st(self, k, off):
        self.emit(f"  have s{k} : St n{k}.mem SV n{k} 0x{off:X} (reg n{k}) := ⟨u{k}.pc, rfl, fun _ => rfl⟩")

    def reg_is(self, k, r, e):
        """A proof that register `r` holds the address of offset `e` of the frame at state k."""
        if lean_val(self.regs[r]) == fa(e):
            return f"g{k}_{r}"
        return f"(by rw [g{k}_{r}]; sv_addr)"


    # --- the checks a stage makes -------------------------------------------------

    def sc_prop(self):
        """The conjunction of the checks, ending in `True`."""
        out = ""
        closes = 0
        for c in self.sc:
            if c[0] == "eq":
                bs = " ".join(c[3])
                out += (f"∃ {bs}, " if bs else "") + f"{c[1]} = {c[2]} ∧ "
            else:
                out += f"({c[1]}) ∧ "
        return out + "True"

    def sc_ok(self, rest):
        """The checks with their witnesses, then `rest`."""
        out = ""
        for c in self.sc:
            if c[0] == "eq":
                bs = " ".join(c[3])
                out += (f"∃ {bs}, " if bs else "") + f"{c[1]} = {c[2]} ∧\n    "
            else:
                out += f"({c[1]}) ∧\n    "
        return out + rest

    def sc_terms(self):
        out = []
        for c in self.sc:
            if c[0] == "eq":
                out += c[3] + [c[4]]
            else:
                out.append(c[2])
        return out

    def fail_proof(self, final):
        """A proof that the checks fail, from `final`: ("eq", hr) for a check
        whose result `hr` is not the one the check wants, or ("prop", h) for a
        proof that the check's proposition is false. The check is the last one
        in `self.sc`."""
        pat, body = [], []
        for i, c in enumerate(self.sc):
            if c[0] == "eq":
                pat += [b + "'" for b in c[3]] + [f"h{i}'"]
            else:
                pat.append(f"h{i}'")
        pat.append("_")
        for i, c in enumerate(self.sc[:-1]):
            if c[0] == "eq":
                body.append(f"rw [{c[4]}] at h{i}'; cases h{i}'")
        last = len(self.sc) - 1
        if final[0] == "eq":
            body.append(f"rw [{final[1]}] at h{last}'; cases h{last}'")
        else:
            body.append(f"exact {final[1]} h{last}'")
        return f"fun ⟨{', '.join(pat)}⟩ => by " + "; ".join(body)

    def reader(self, k, dc):
        """The address, length, and `SvIn` proof of the reader at offset `dc`."""
        rp, rl = lean_val(self.words[dc + 8]), lean_val(self.words[dc + 12])
        return rp, rl, self.slices[(rp, rl)]

    def call_head(self, k, off, wrapper, named, outs):
        self.emit(f"  -- 0x{off:X}: {wrapper}")
        self.emit(f"  obtain ⟨n{k}, {', '.join(outs)}⟩ := {wrapper} {named}")

    def der_args(self, k, off, oc, dc, extra_a=None, rsp=True, tag=None):
        a0 = self.reg_is(k - 1, 10, oc)
        a1 = self.reg_is(k - 1, 11, dc)
        parts = [f"F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide)"]
        if rsp:
            parts.append(f"g{k-1}_2")
        parts.append(f"{a0} {a1}")
        if tag is not None:
            parts.append(f"g{k-1}_12 (by decide)")
        return " ".join(parts)

    def frame_after(self, k, ranges, words, byts=None, accs=None):
        """Frame facts after a call that kept all but `ranges`, with `words`
        (offset -> (value, proof)), `byts`, and `accs` (offset -> (limbs,
        value, proof)) written."""
        self.keep_frame(k, ("L", ranges))
        for d, (n, v, pf) in sorted((accs or {}).items()):
            self.acc[d] = (n, v)
            self.emit(f"  have a{k}_{d:x} : {self.acc_stmt(k, d, n, v)} := {pf}")
        for e, (v, pf) in sorted(words.items()):
            self.words[e] = ("U", v)
            self.emit(f"  have w{k}_{e:x} : {self.word_stmt(k, e, ('U', v))} := {pf}")
        for e, (v, pf) in sorted((byts or {}).items()):
            self.bytes[e] = v
            self.emit(f"  have b{k}_{e:x} : {self.byte_stmt(k, e, v)} := {pf}")
        self.end_step()

    def elem(self, off, oc, dc, tag):
        """`Der::element` with tag `tag`. Returns (k, the result's expression, the reader)."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_elemF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X}) (tag := 0x{tag:X})",
                       [f"c{k}", f"s{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc, rsp=False, tag=tag)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at Ok{k} Er{k}")
        self.keep_regs(k, [r for r in range(32) if r not in (1, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17)],
                       lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        return k, f"derElement 0x{tag:X} (memBytes M0 ({rp}) ({rl}).toNat)", (rp, rl, inp)

    def elem_ok(self, k, oc, dc, t, rd):
        rp, rl, inp = rd
        hr = f"hr{k}"
        self.emit(f"  obtain ⟨o0_{k}, o4_{k}, o8_{k}, o12_{k}, o16_{k}, d8_{k}, d12_{k}⟩ := Ok{k} {t} {hr}")
        h = f"BitVec.ofNat 32 {t}.header"
        hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
        words = {oc: (f"({rp}) + {h}", f"o0_{k}"), oc + 4: (f"BitVec.ofNat 32 {t}.len", f"o4_{k}"),
                 oc + 8: (f"{rp}", f"o8_{k}"), oc + 12: (hl, f"o12_{k}"),
                 dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")}
        self.frame_after(k, [(oc, 17), (dc + 8, 8)], words, {oc + 16: (f"BitVec.ofNat 8 {t}.tag", f"o16_{k}")})
        self.slices[(f"({rp}) + {h}", f"BitVec.ofNat 32 {t}.len")] = f"({inp}.contentW {hr})"
        self.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW {hr})"
        self.slices[(f"{rp}", hl)] = f"({inp}.rawW {hr})"
        self.slices_nat[(f"{rp}", f"{t}.header + {t}.len")] = f"({inp}.rawN {hr})"

    def elem_split(self, k, expr, oc, dc, rd, fail_tail, exit_lemma="sv_fail"):
        """Splits on `Der::element`'s result; the failing case reads the null
        address and runs `fail_tail` from there. Returns the `DerTlv` name."""
        t = f"tl{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {expr} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with er{k} | {t}")
        self.sc.append(("eq", expr, f".ok {t}", [t], f"hr{k}"))

        self.fork(lambda sub: fail_elem(sub, k, oc, dc, f"hr{k}", f"Er{k} er{k} hr{k}", 17, fail_tail, exit_lemma))
        self.elem_ok(k, oc, dc, t, rd)
        return t


    def split_on(self, k, expr, fail_pat, ok_pat, ok_val, binders, fail_body):
        """Splits on `expr`: the failing case `fail_pat` closes with `fail_body`,
        and the check `expr = ok_pat` joins the stage's checks."""
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {expr} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with {fail_pat} | {ok_pat}")
        self.sc.append(("eq", expr, ok_val, binders, f"hr{k}"))
        self.fork(fail_body)

    def prop_check(self, P, hname, fail_body):
        """Splits on the proposition `P`; the failing case closes with `fail_body`."""
        self.emit(f"  by_cases {hname} : {P}")
        self.emit("  rotate_left")
        self.sc.append(("prop", P, hname))
        self.fork(fail_body)

    def bits(self, off, oc, dc, fail_tail):
        """`Der::bit_string`, split on the element and then on the bits."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_bitsF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k} Ok{k} Er{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
        el = f"derElement 3 {L}"
        t = f"tl{k}"

        self.split_on(k, el, f"er{k}", t, f".ok {t}", [t],
                      lambda sub: fail_elem(sub, k, oc, dc, f"hr{k}", f"Er{k} er{k} (by rw [hr{k}]; rfl)", 8, fail_tail))
        bv = f"derBitsOf {L} ({rp}) (.ok {t})"
        k2 = f"{k}b"

        self.emit(f"  obtain ⟨r{k2}, hr{k2}⟩ : ∃ r, {bv} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k2} with er{k2} | ⟨bp{k}, bl{k}⟩")
        self.sc.append(("eq", bv, f".ok (bp{k}, bl{k})", [f"bp{k}", f"bl{k}"], f"hr{k2}"))
        self.fork(lambda sub: fail_elem(sub, k, oc, dc, f"hr{k2}", f"Er{k} er{k2} (by rw [hr{k}, hr{k2}])", 8, fail_tail))
        self.emit(f"  obtain ⟨p0_{k}, p4_{k}⟩ := Ok{k} bp{k} bl{k} (by rw [hr{k}, hr{k2}])")
        self.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} {t} hr{k}")
        hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
        words = {oc: (f"bp{k}", f"p0_{k}"), oc + 4: (f"bl{k}", f"p4_{k}"),
                 dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")}
        self.frame_after(k, [(oc, 8), (dc + 8, 8)], words)
        self.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hr{k})"
        self.slices[(f"bp{k}", f"bl{k}")] = f"({inp}.bitsW hr{k} hr{k2})"
        return k


    def jump(self, off):
        text, ln = INSTR[off]
        tgt = off + s32(int(tokens(text)[2], 16))
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: j")
        self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.jump E{k-1}.self sv_at_{off:x} (off' := 0x{tgt:X}) (by decide)")
        self.emit(f"    (by rw [s{k-1}.pc]; decide)")
        self.st(k, tgt)
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"(.single d{k})", f"fr{k}", f"V{k-1}.same m{k}")
        self.keep_regs(k, range(32), lambda r: f"u{k}.regs")
        self.keep_frame(k, ("same",))
        self.end_step()
        return tgt

    def opt(self, off, oc, dc, tag):
        """`Der::optional`; returns k and the result's expression."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_optF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X}) (tag := 0x{tag:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc, tag=tag)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at R{k}")
        self.keep_regs(k, [r for r in range(32) if r not in (1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30)],
                       lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        return k, f"derOptRes 0x{tag:X} (memBytes M0 ({rp}) ({rl}).toNat)", (rp, rl, inp)

    def opt2(self, off, oc, dc, tag):
        """`Der::optional` through `sv_optF2`; returns k and the result's
        expression. `N{k}` says the reader is left alone when the tag is absent."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_optF2", f"(oc := 0x{oc:X}) (dc := 0x{dc:X}) (tag := 0x{tag:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"R{k}", f"N{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc, tag=tag)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at R{k} N{k}")
        self.keep_regs(k, [r for r in range(32) if r not in (1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30)],
                       lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        return k, f"derOptRes 0x{tag:X} (memBytes M0 ({rp}) ({rl}).toNat)", (rp, rl, inp)

    def iis(self, off, dc):
        """`Der::integer_is` with the expected value in `a1`; returns k and the result's expression."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_iiF", f"(dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2 {self.reg_is(k - 1, 10, dc)}")
        self.emit(f"    (by decide) (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        a1 = lean_val(self.regs[11])
        self.emit(f"  rw [sv_mb fR{k-1} {inp}, derIntIsOf_congr fR{k-1} {inp}, g{k-1}_11] at R{k}")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.regs.pop(2, None)
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
        return k, f"derIntIsOf M0 {L} ({rp}) (derElement 2 {L}) (({a1}).extractLsb' 0 8)", (rp, rl, inp)


    def pos(self, off, oc, dc, fail_tail, exit_lemma="sv_fail"):
        """`Der::positive_integer`, split on the element and then on the integer.
        Returns k and the names of the integer's address and length."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_posF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k} Ok{k} Er{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
        t = f"tl{k}"
        self.split_on(k, f"derElement 2 {L}", f"er{k}", t, f".ok {t}", [t],
                      lambda sub: fail_elem(sub, k, oc, dc, f"hr{k}", f"Er{k} er{k} (by rw [hr{k}]; rfl)", 8, fail_tail, exit_lemma))
        pv = f"derPosIntOf {L} ({rp}) (.ok {t})"
        k2 = f"{k}b"
        self.emit(f"  obtain ⟨r{k2}, hr{k2}⟩ : ∃ r, {pv} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k2} with er{k2} | ⟨ip{k}, il{k}⟩")
        self.sc.append(("eq", pv, f".ok (ip{k}, il{k})", [f"ip{k}", f"il{k}"], f"hr{k2}"))
        self.fork(lambda sub: fail_elem(sub, k, oc, dc, f"hr{k2}", f"Er{k} er{k2} (by rw [hr{k}, hr{k2}])", 8, fail_tail, exit_lemma))
        self.emit(f"  obtain ⟨p0_{k}, p4_{k}⟩ := Ok{k} ip{k} il{k} (by rw [hr{k}, hr{k2}])")
        self.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} {t} hr{k}")
        hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
        self.frame_after(k, [(oc, 8), (dc + 8, 8)],
                         {oc: (f"ip{k}", f"p0_{k}"), oc + 4: (f"il{k}", f"p4_{k}"),
                          dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")})
        self.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hr{k})"
        return k, (rp, rl, inp)

    def nestr(self, off, oc, dc, wrapper, tag, extra=""):
        """`Der::sequence`, `Der::set`, or `Der::nested` (`wrapper`) on the reader at
        `dc`, for elements with tag `tag`. Returns (k, expression, reader)."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, wrapper, f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)}{extra} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at Ok{k} Er{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        return k, f"derElement 0x{tag:X} (memBytes M0 ({rp}) ({rl}).toNat)", (rp, rl, inp)

    def issha(self, off, dc):
        """`tsa::is_sha256` on the reader at `dc`; returns k and the result's expression."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_isShaF", f"(dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (D0.sv F fR{k-1}) s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, dc)} (by decide) (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [isSha256Of_congr (sv_pt fR{k-1} {inp})] at R{k}")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k, f"isSha256Of M0 ({rp}) ({rl}).toNat", (rp, rl, inp)

    def seqr(self, off, oc, dc):
        """`Der::sequence` on the reader at `dc`. Returns (k, expression, reader)."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_seqF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at Ok{k} Er{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        return k, f"derElement 0x30 (memBytes M0 ({rp}) ({rl}).toNat)", (rp, rl, inp)

    def seq_ok(self, k, oc, dc, t, rd):
        rp, rl, inp = rd
        self.emit(f"  obtain ⟨o0_{k}, o4_{k}, o8_{k}, o12_{k}, d8_{k}, d12_{k}⟩ := Ok{k} {t} hr{k}")
        h = f"BitVec.ofNat 32 {t}.header"
        hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
        words = {oc: (f"({rp}) + {h}", f"o0_{k}"), oc + 4: (f"BitVec.ofNat 32 {t}.len", f"o4_{k}"),
                 oc + 8: (f"({rp}) + {h}", f"o8_{k}"), oc + 12: (f"BitVec.ofNat 32 {t}.len", f"o12_{k}"),
                 dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")}
        self.frame_after(k, [(oc, 16), (dc + 8, 8)], words)
        self.slices[(f"({rp}) + {h}", f"BitVec.ofNat 32 {t}.len")] = f"({inp}.contentW hr{k})"
        self.slices_nat[(f"({rp}) + {h}", f"{t}.len")] = f"({inp}.content hr{k})"
        self.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hr{k})"

    def alg(self, off, oc, dc):
        """`Der::algorithm`. Returns (k, expression, the bytes' address, their `SvIn`)."""
        k = self.k = self.k + 1
        p = lean_val(self.words[dc + 8])
        lw = lean_val(self.words[dc + 12])
        nl = nat_of(lw)
        inp = self.slices_nat[(p, nl)]
        self.call_head(k, off, "sv_algF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X}) (nl := {nl})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [derAlgOf_congr (sv_pt fR{k-1} {inp})] at R{k}")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k, f"derAlgOf M0 ({p}) ({nl})", p, inp

    def alg_w(self, off, oc, dc):
        """`Der::algorithm` on a reader whose length is a word; returns (k,
        expression, the bytes' address, their `SvIn`)."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        nl = f"({rl}).toNat"
        self.call_head(k, off, "sv_algF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X}) (nl := {nl})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} (by rw [w{k-1}_{dc + 12:x}, ofNat_toNat_self]) {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [derAlgOf_congr (sv_pt fR{k-1} {inp})] at R{k}")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k, f"derAlgOf M0 ({rp}) ({nl})", (rp, rl, inp)

    def sne(self, off, p, pl, q, ql, hp, hq, ha1=None, ha3=None):
        """`<[u8]>::ne` of `pl` bytes at `p` and `ql` at `q`; returns k. The result in
        `a0` is left to the caller."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_sneF", f"(pl := {pl}) (ql := {ql})",
                       [f"c{k}", f"s{k}", f"rk{k}", f"a0_{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    g{k-1}_10 {ha1 or f'g{k-1}_11'} g{k-1}_12 {ha3 or f'g{k-1}_13'} {hp} {hq}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mbRo F fR{k-1} {hp}, sv_mbRo F fR{k-1} {hq}] at a0_{k}")
        self.keep_regs(k, [r for r in range(32) if r not in (1, 6, 10, 11, 12, 13, 14)],
                       lambda r: f"rk{k} {rname(r)} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)")
        self.frame_after(k, [], {})
        return k


    def rt(self, off, oc, dc, alias=None):
        """`x509::read_time`; returns (k, expression, the reader's address, length, and `SvIn`)."""
        k = self.k = self.k + 1
        rp = lean_val(self.words[dc + 8])
        lw = lean_val(self.words[dc + 12])
        rl = nat_of(lw)
        inp = self.slices_nat[(rp, rl)]
        self.call_head(k, off, "sv_rtF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X}) (rl := {rl})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at Ok{k} Er{k}")
        if alias:
            self.emit(f"  rw [← {alias}] at Ok{k} Er{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        bytes_ = alias_bytes = f"(memBytes M0 ({rp}) ({rl}))"
        return k, bytes_, rp, rl, inp

    def rt_split(self, k, bytes_, oc, dc, rp, rl, inp, fail_tail):
        """Splits on `readTime`; returns the names of the time, the rest, and the
        proof that the rest is the reader's bytes."""
        ex = f"readTime {bytes_}"
        nb, rb = f"tm{k}", f"rs{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with _ | ⟨{nb}, {rb}⟩")
        self.sc.append(("eq", ex, f"some ({nb}, {rb})", [nb, rb], f"hr{k}"))

        self.fork(lambda sub: rt_fail(sub, k, oc, dc, fail_tail))
        self.emit(f"  obtain ⟨h64_{k}, y0_{k}, y8_{k}, y12_{k}, kk{k}, hkk{k}, d8_{k}, d12_{k}, hrb{k}⟩ := Ok{k} {nb} {rb} hr{k}")
        self.emit(f"  rw [sv_mb fR{k-1} ({inp}.drop hkk{k})] at hrb{k}")
        self.pinned |= {f"kk{k}", f"hkk{k}", f"hrb{k}", f"h64_{k}"}
        rp2, rl2 = f"({rp}) + BitVec.ofNat 32 kk{k}", f"({rl}) - kk{k}"
        self.frame_after(k, [(oc, 16), (dc + 8, 8)],
                         {oc + 8: (f"BitVec.ofNat 32 ({nb} % 2 ^ 32)", f"y8_{k}"),
                          oc + 12: (f"BitVec.ofNat 32 ({nb} / 2 ^ 32)", f"y12_{k}"),
                          dc + 8: (rp2, f"d8_{k}"), dc + 12: (f"BitVec.ofNat 32 ({rl2})", f"d12_{k}")},
                         {oc: ("(0 : BitVec 8)", f"y0_{k}")})
        self.slices_nat[(rp2, rl2)] = f"({inp}.drop hkk{k})"
        return nb, rb, f"hrb{k}"


    def seq_split(self, k, ex, oc, dc, rd, lw_off, lbu_off, br_off):
        """Splits on `Der::sequence`'s result; the failing case reads the null
        address and the error code and branches to 0x966. Returns the `DerTlv` name."""
        t = f"tl{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with er{k} | {t}")
        self.sc.append(("eq", ex, f".ok {t}", [t], f"hr{k}"))
        self.fork(lambda sub: seq_fail(sub, k, oc, dc, lw_off, lbu_off, br_off))
        self.seq_ok(k, oc, dc, t, rd)
        self.load(lw_off, "lw")
        self.load(lbu_off, "lbu")
        reg = reg_of(tokens(INSTR[br_off][0])[2])
        self.branch(br_off, False, f"by rw [g{self.k}_{reg}, s{self.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
        return t

    def seqeq(self, off, p, pl, q, ql, hp, hq, ha3=None, ha1=None):
        """`<[u8]>::eq` of `pl` bytes at `p` and `ql` at `q`; returns k."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_seqEqF", f"(pl := {pl}) (ql := {ql})",
                       [f"c{k}", f"s{k}", f"rk{k}", f"a0_{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    g{k-1}_10 {ha1 or f'g{k-1}_11'} g{k-1}_12 {ha3 or f'g{k-1}_13'} {hp} {hq}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mbRo F fR{k-1} {hp}, sv_mbRo F fR{k-1} {hq}] at a0_{k}")
        self.keep_regs(k, [r for r in range(32) if r not in (1, 6, 10, 11, 12, 13, 14)],
                       lambda r: f"rk{k} {rname(r)} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)")
        self.frame_after(k, [], {})
        return k

    def set_a0(self, k, val, how):
        """`a0` after a comparison at step `k` is the constant `val`."""
        self.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 {val} := by rw [a0_{k}, {how}]; rfl")
        self.regs[10] = ("C", val)


    def load_in(self, off, inp, pos="(by omega)"):
        """`lbu` or `lb` of a byte outside the stack, whose `SvIn` is `inp`."""
        text, ln = INSTR[off]
        tk = tokens(text)
        kind = tk[1]
        rd, base, imm = reg_of(tk[2]), reg_of(tk[3]), int(tk[4], 16)
        p = lean_val(self.regs[base])
        addr = p if imm == 0 else f"({p}) + 0x{imm:X}"
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: {kind[1:]} from the bundle")
        lemma = "s{0}.lbu".format(k - 1) if kind == ".lbu" else "St.lb s{0}".format(k - 1)
        self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := {lemma} E{k-1}.self sv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
        self.st(k, off + ln)
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"(.single d{k})", f"fr{k}", f"V{k-1}.same m{k}")
        new = {}
        for r, v in sorted(self.regs.items()):
            if r == rd:
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [u{k}.regs, upd_ne (by decide) (by decide), g{k-1}_{r}]")
            new[r] = v
        ext = "zeroExtend" if kind == ".lbu" else "signExtend"
        vstr = f"(M0 ({addr})).{ext} 32"
        self.emit(f"  have g{k}_{rd} : reg n{k} {rname(rd)} = {vstr} := by")
        self.emit(f"    rw [u{k}.regs]; simp +decide only [upd, ↓reduceIte]")
        if imm == 0:
            self.emit(f"    rw [g{k-1}_{base}, show ({p}) + 0x0 = {p} from BitVec.add_zero _, fR{k-1} _ ({inp}.r0 {pos})]")
        else:
            self.emit(f"    rw [g{k-1}_{base}, fR{k-1} _ ({inp}.r0 {pos})]")
        new[rd] = ("U", vstr)
        self.regs = new
        self.keep_frame(k, ("same",))
        self.end_step()

    def gs(self, off, oc, inp):
        """`VerifyingKey::from_sec1_bytes` on the 65 bytes `a1` points at; returns k."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_gsF", f"(oc := 0x{oc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (P2Data.sv F D0 fR{k-1}) s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} g{k-1}_11 (by decide) (by decide) {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [gsOk_congr (sv_pt fR{k-1} {inp})] at Ok{k} Er{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k


    def oid(self, off, oc, dc, fail_tail, exit_lemma="sv_fail"):
        """`Der::oid` on the reader at `dc`, split on its result. Returns k and the
        names of the OID's content address and length."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_oidF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k} Ok{k} Er{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
        ex = f"derContent ({rp}) (derOid {L})"
        op, ol = f"op{k}", f"ol{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with er{k} | ⟨{op}, {ol}⟩")
        self.sc.append(("eq", ex, f".ok ({op}, {ol})", [op, ol], f"hr{k}"))

        self.fork(lambda sub: oid_fail(sub, k, oc, dc, fail_tail, exit_lemma))
        to = f"to{k}"
        self.emit(f"  obtain ⟨{to}, ht{k}, -, -⟩ := oid_ok_content hr{k}")
        self.sc.append(("eq", f"derOid {L}", f".ok {to}", [to], f"ht{k}"))
        self.emit(f"  obtain ⟨p0_{k}, p4_{k}⟩ := Ok{k} {op} {ol} hr{k}")
        self.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} {to} (derOid_ok_elem ht{k})")
        hl = f"BitVec.ofNat 32 ({to}.header + {to}.len)"
        self.frame_after(k, [(oc, 8), (dc + 8, 8)],
                         {oc: (op, f"p0_{k}"), oc + 4: (ol, f"p4_{k}"),
                          dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")})
        self.slices[(op, ol)] = f"({inp}.oidIn hr{k})"
        self.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW (derOid_ok_elem ht{k}))"
        return k, op, ol


    def exit_here(self):
        """This fork reaches the stage's end too; `finish` writes its conclusion."""
        tag = f"@@EXIT{len(self.exits)}@@"
        self.emit("  " + tag)
        self.exits.append((tag, self))

    def oct(self, off, oc, dc, fail_tail, exit_lemma="sv_fail"):
        """`Der::octet_string` on the reader at `dc`, split on its result. Returns k
        and the names of the content's address and length."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_octF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k} Ok{k} Er{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
        ex = f"derContent ({rp}) (derElement 4 {L})"
        vp, vl = f"vp{k}", f"vl{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with er{k} | ⟨{vp}, {vl}⟩")
        self.sc.append(("eq", ex, f".ok ({vp}, {vl})", [vp, vl], f"hr{k}"))
        self.fork(lambda sub: oid_fail(sub, k, oc, dc, fail_tail, exit_lemma))
        te = f"te{k}"
        self.emit(f"  obtain ⟨{te}, ht{k}, -, -⟩ := content_ok_elem hr{k}")
        self.sc.append(("eq", f"derElement 4 {L}", f".ok {te}", [te], f"ht{k}"))
        self.emit(f"  obtain ⟨p0_{k}, p4_{k}⟩ := Ok{k} {vp} {vl} hr{k}")
        self.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} {te} ht{k}")
        hl = f"BitVec.ofNat 32 ({te}.header + {te}.len)"
        self.frame_after(k, [(oc, 8), (dc + 8, 8)],
                         {oc: (vp, f"p0_{k}"), oc + 4: (vl, f"p4_{k}"),
                          dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")})
        self.slices[(vp, vl)] = f"({inp}.contentIn hr{k})"
        self.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW ht{k})"
        return k, vp, vl

    def lo(self, off, p, nl, q, ql, hp, hq, ha1=None):
        """`der::lists_oid`; returns k. Its result in `a0` and `a1` is left to the caller."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_loF", f"(nl := {nl}) (ql := {ql})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"R{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    g{k-1}_10 {ha1 or f'g{k-1}_11'} g{k-1}_12 (by rw [g{k-1}_13, ofNat_toNat_self]) {hp} {hq}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [listsOidOf, listsOidLoop_congr _ _ _ (sv_pt fR{k-1} {hp}), sv_mb fR{k-1} {hq}, ← listsOidOf] at R{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.frame_after(k, [], {})
        return k

    def load_data(self, off, val, i):
        """`lw` of the constant word at offset `i` of `svConst`, `val`."""
        text, ln = INSTR[off]
        tk = tokens(text)
        rd, base, imm = reg_of(tk[2]), reg_of(tk[3]), int(tk[4], 16)
        bv = self.regs[base]
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: lw of a constant")
        self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.lw E{k-1}.self sv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
        self.emit(f"    (by rw [g{k-1}_{base}]; decide)")
        self.st(k, off + ln)
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"(.single d{k})", f"fr{k}", f"V{k-1}.same m{k}")
        new = {}
        for r, v in sorted(self.regs.items()):
            if r == rd:
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [u{k}.regs, upd_ne (by decide) (by decide), g{k-1}_{r}]")
            new[r] = v
        self.emit(f"  have g{k}_{rd} : reg n{k} {rname(rd)} = BitVec.ofNat 32 0x{val:X} := by")
        self.emit(f"    rw [u{k}.regs]; simp +decide only [upd, ↓reduceIte]")
        self.emit(f"    rw [g{k-1}_{base}, show {lean_val(bv)} + 0x{imm & 0xFFFFFFFF:X} = SVK + BitVec.ofNat 32 0x{i:X} by decide]")
        self.emit(f"    exact (SvData.sv F SD0 fR{k-1}).w32 (by decide) (by decide)")
        new[rd] = ("C", val)
        self.regs = new
        self.keep_frame(k, ("same",))
        self.end_step()


    def boolt(self, off, dc):
        """`Der::boolean_true` on the reader at `dc`; returns (k, expression, reader)."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_boolF", f"(dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"a0_{k}", f"K{k}", f"A{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2 {self.reg_is(k - 1, 10, dc)}")
        self.emit(f"    (by decide) (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at a0_{k} A{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
        return k, f"derBoolOf {L} (derElement 1 {L})", (rp, rl, inp)


    def tlv(self, off, oc, dc, fail_tail, exit_lemma="sv_fail"):
        """`Der::tlv` on the reader at `dc`, split on its result; returns k. The
        element's name is in `last_tlv`."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_tlvF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) {self.reg_is(k - 1, 10, oc)}")
        self.emit(f"    {self.reg_is(k - 1, 11, dc)} (by decide) (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at Ok{k} Er{k}")
        self.keep_regs(k, [r for r in range(32) if r not in (1, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17)],
                       lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        ex = f"derTlv (memBytes M0 ({rp}) ({rl}).toNat)"
        t = f"tl{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with er{k} | {t}")
        self.sc.append(("eq", ex, f".ok {t}", [t], f"hr{k}"))
        self.fork(lambda sub: fail_elem(sub, k, oc, dc, f"hr{k}", f"Er{k} er{k} hr{k}", 17, fail_tail, exit_lemma))
        self.elem_ok(k, oc, dc, t, (rp, rl, inp))
        self.last_tlv = t
        return k


    def intc(self, off, oc, dc):
        """`Der::integer` on the reader at `dc`; returns (k, expression, reader). The caller splits."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_intF", f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    {self.der_args(k, off, oc, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k} Ok{k} Er{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
        return k, f"derIntOf {L} ({rp}) (derElement 2 {L})", (rp, rl, inp)


    def es(self, off, oc, p, nl, inp):
        """`der::ecdsa_signature::<48>` on `nl` bytes at `p`, split on its result;
        returns k. The success case's `r` and `s` are `sr{k}` and `ss{k}`."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_esF", f"(oc := 0x{oc:X}) (nl := {nl})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} g{k-1}_11 g{k-1}_12 (by decide) {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [ecdsaSigOf_congr (sv_pt fR{k-1} {inp})] at R{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        ex = f"ecdsaSigOf 48 M0 ({p}) ({nl})"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with eb{k} | ⟨sr{k}, ss{k}⟩")
        self.sc.append(("eq", ex, f".ok (sr{k}, ss{k})", [f"sr{k}", f"ss{k}"], f"hr{k}"))

        self.fork(lambda sub: es_fail(sub, k, off, oc))
        self.emit(f"  rw [hr{k}] at R{k}")
        self.emit(f"  obtain ⟨y0_{k}, yr_{k}, ys_{k}⟩ := R{k}")
        self.emit(f"  have q{k}_{oc + 1:x} : ∀ j, j < 48 → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{oc + 1:X} + j)) = "
                  f"BitVec.ofNat 8 ((sr{k}).getD j 0) := fun j hj => by rw [show 0x{oc + 1:X} + j = 0x{oc:X} + 1 + j by omega]; exact yr_{k} j hj")
        self.emit(f"  have q{k}_{oc + 49:x} : ∀ j, j < 48 → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{oc + 49:X} + j)) = "
                  f"BitVec.ofNat 8 ((ss{k}).getD j 0) := fun j hj => by rw [show 0x{oc + 49:X} + j = 0x{oc:X} + 49 + j by omega]; exact ys_{k} j hj")
        self.frame_after(k, [(oc, 97)], {}, {oc: ("(0 : BitVec 8)", f"y0_{k}")})
        self.ranges[oc + 1] = (48, f"BitVec.ofNat 8 ((sr{k}).getD j 0)")
        self.ranges[oc + 49] = (48, f"BitVec.ofNat 8 ((ss{k}).getD j 0)")
        self.load(off + 8, "lbu")
        self.load(off + 0xC, "lbu")
        self.branch(off + 0x10, False, f"by rw [g{self.k}_10, s{self.k}.zero]; decide")
        return k


    def es2(self, off, oc, p, nl, inp, ha2):
        """`der::ecdsa_signature::<48>` as `es`, followed by `lbu a0`, `lbu s9`, and
        `beqz a0` taken on success; the failing case moves `s9` to `s0` and jumps
        to 0x2C60."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_esF", f"(oc := 0x{oc:X}) (nl := {nl})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} g{k-1}_11 {ha2} (by decide) {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [ecdsaSigOf_congr (sv_pt fR{k-1} {inp})] at R{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        ex = f"ecdsaSigOf 48 M0 ({p}) ({nl})"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with eb{k} | ⟨sr{k}, ss{k}⟩")
        self.sc.append(("eq", ex, f".ok (sr{k}, ss{k})", [f"sr{k}", f"ss{k}"], f"hr{k}"))
        self.fork(lambda sub: es2_fail(sub, k, off, oc))
        self.emit(f"  rw [hr{k}] at R{k}")
        self.emit(f"  obtain ⟨y0_{k}, yr_{k}, ys_{k}⟩ := R{k}")
        self.emit(f"  have q{k}_{oc + 1:x} : ∀ j, j < 48 → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{oc + 1:X} + j)) = "
                  f"BitVec.ofNat 8 ((sr{k}).getD j 0) := fun j hj => by rw [show 0x{oc + 1:X} + j = 0x{oc:X} + 1 + j by omega]; exact yr_{k} j hj")
        self.emit(f"  have q{k}_{oc + 49:x} : ∀ j, j < 48 → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{oc + 49:X} + j)) = "
                  f"BitVec.ofNat 8 ((ss{k}).getD j 0) := fun j hj => by rw [show 0x{oc + 49:X} + j = 0x{oc:X} + 49 + j by omega]; exact ys_{k} j hj")
        self.frame_after(k, [(oc, 97)], {}, {oc: ("(0 : BitVec 8)", f"y0_{k}")})
        self.ranges[oc + 1] = (48, f"BitVec.ofNat 8 ((sr{k}).getD j 0)")
        self.ranges[oc + 49] = (48, f"BitVec.ofNat 8 ((ss{k}).getD j 0)")
        self.load(off + 8, "lbu")
        self.load(off + 0xC, "lbu")
        self.branch(off + 0x10, True, f"by rw [g{self.k}_10, s{self.k}.zero]; decide")
        return k

    def digest_stmt(self, k, oc, ex):
        return f"memBytes n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 0x{oc:X}) 32 = {ex}"

    def sha256(self, off, oc, p, nl, inp, ha2, hn):
        """`c3_crypto::sha::sha256` of the `nl` bytes at `p` into offset `oc`."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_sha256F", f"(oc := 0x{oc:X}) (nl := {nl})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"D{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (S2.sv F KS fR{k-1}) KS s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} g{k-1}_11 {ha2} (by decide) {inp} {hn}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mbRo F fR{k-1} {inp}] at D{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.pinned.add(f"D{k}")
        self.frame_after(k, [(oc, 32)], {})
        self.digest = (k, oc, f"sha256 (memBytes M0 ({p}) ({nl}))")
        return k

    def carry_digest(self):
        """The digest survives a step that left memory alone."""
        kd, oc, ex = self.digest
        k = self.k
        self.emit(f"  have D{k} : {self.digest_stmt(k, oc, ex)} := by rw [m{k}]; exact D{kd}")
        self.pinned.add(f"D{k}")
        self.digest = (k, oc, ex)

    def a32ne(self, off, oc, q, qin):
        """`<[u8; 32]>::ne` of the digest at offset `oc` and the 32 bytes at `q`.
        The result in `a0` is left to the caller."""
        kd, ocd, ex = self.digest
        assert ocd == oc and kd == self.k
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_a32neF", f"(oc := 0x{oc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"a0_{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} g{k-1}_11 (by decide) {qin}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [D{kd}, sv_mbRo F fR{k-1} {qin}] at a0_{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.frame_after(k, [], {})
        return k

    def parts2(self, off, oc, pc, p0, l0, r0, p1, l1, r1, hl0, hl1, hn0, hn1):
        """`c3_crypto::sha::sha256_parts` of two slices whose descriptors are at
        offset `pc`, into offset `oc`."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_sha256P2F", f"(oc := 0x{oc:X}) (pc := 0x{pc:X}) (l0 := {l0}) (l1 := {l1})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"D{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (S2.sv F KS fR{k-1}) KS s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} {self.reg_is(k - 1, 11, pc)} g{k-1}_12 (by decide) (by decide) (by decide)")
        self.emit(f"    w{k-1}_{pc:x} {hl0} w{k-1}_{pc + 8:x} {hl1} {r0} {r1} {hn0} {hn1}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mbRo F fR{k-1} {r0}, sv_mbRo F fR{k-1} {r1}] at D{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.pinned.add(f"D{k}")
        self.frame_after(k, [(oc, 32)], {})
        self.digest = (k, oc, f"sha256 (memBytes M0 ({p0}) ({l0}) ++ memBytes M0 ({p1}) ({l1}))")
        return k

    def line(self, off, oc, p, nl, inp, ha2, fail_tail):
        """`checkpoint::line` on the `nl` bytes at `p`, split on the newline's
        index; the failing case runs `fail_tail`. Returns (k, the index's name,
        and the rest's address, length, and `SvRo`)."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_lineF", f"(oc := 0x{oc:X}) (nl := {nl})",
                       [f"c{k}", f"s{k}", f"rk{k}", f"K{k}", f"L{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (CK0.sv F fR{k-1}) s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide)")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} g{k-1}_11 {ha2} (by decide) (by decide) {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [nlScan_ro F fR{k-1} {inp}] at L{k}")
        self.keep_regs(k, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        ex = f"nlScan M0 ({p}) 0 ({nl})"
        ix = f"ix{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with _ | {ix}")
        self.sc.append(("eq", ex, f"some {ix}", [ix], f"hr{k}"))
        self.fork(lambda sub: sub.line_none(k, oc, fail_tail))
        self.pinned |= {f"hix{k}"}
        self.emit(f"  have hix{k} : {ix} < {nl} := by have := (nlScan_lt _ _ _ hr{k}).2; omega")
        self.emit(f"  rw [hr{k}] at L{k}")
        self.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, y12_{k}⟩ := L{k}")
        rp = f"({p}) + BitVec.ofNat 32 ({ix} + 1)"
        self.frame_after(k, [(oc, 16)], {oc: (p, f"y0_{k}"), oc + 4: (f"BitVec.ofNat 32 {ix}", f"y4_{k}"),
                                         oc + 8: (rp, f"y8_{k}"),
                                         oc + 12: (f"BitVec.ofNat 32 ({nl}) - BitVec.ofNat 32 ({ix} + 1)", f"y12_{k}")})
        return k, ix, rp, f"({nl}) - ({ix} + 1)", f"(line_rest {inp} hix{k})"

    def line_none(self, k, oc, fail_tail):
        self.emit(f"  rw [hr{k}] at L{k}")
        self.emit(f"  obtain ⟨z0_{k}, z4_{k}⟩ := L{k}")
        self.frame_after(k, [(oc, 16)], {oc: ("0", f"z0_{k}")}, {oc + 4: ("(0x1A : BitVec 8)", f"z4_{k}")})
        fail_tail(self)
        self.load_any(0x2FEA)
        self.jump(0x2FEE)
        self.fail(self.fail_proof(("eq", f"hr{k}")))

    def ms(self, off, c, N):
        """`memset` of `N` bytes at offset `c`."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_ms2F", f"(c := 0x{c:X}) (N := 0x{N:X})",
                       [f"c{k}", f"s{k}", f"rk{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide)")
        self.emit(f"    {self.reg_is(k - 1, 10, c)} g{k-1}_11 g{k-1}_12 (by decide)")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.keep_regs(k, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.frame_after(k, [(c, N)], {})
        return k

    def b64(self, off, rc, oc, t, nl, inp, ha2, L):
        """`base64::decode_into` of the `nl` bytes at `t`; returns k and the
        expression of the decoded bytes. The caller splits."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_b64F", f"(rc := 0x{rc:X}) (oc := 0x{oc:X}) (nl := {nl}) (L := {L})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Bad{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (CK0.sv F fR{k-1}) s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, rc)} g{k-1}_11 {ha2} {self.reg_is(k - 1, 13, oc)} g{k-1}_14")
        self.emit(f"    (by decide) (by decide) (by decide) (by decide) {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mbRo F fR{k-1} {inp}] at Ok{k} Bad{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k, f"base64Decode (memBytes M0 ({t}) ({nl}))"

    def parts4(self, off, oc, pc, parts):
        """`c3_crypto::sha::sha256_parts` of four slices whose descriptors are at
        offset `pc`; `parts` lists (address, length, `SvRo`, length fact, bound)."""
        k = self.k = self.k + 1
        ls = " ".join(f"(l{i} := {pt[1]})" for i, pt in enumerate(parts))
        self.call_head(k, off, "sv_sha256P4F", f"(oc := 0x{oc:X}) (pc := 0x{pc:X}) {ls}",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"D{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (S2.sv F KS fR{k-1}) KS s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} {self.reg_is(k - 1, 11, pc)} g{k-1}_12 (by decide) (by decide) (by decide)")
        self.emit("    " + " ".join(f"w{k-1}_{pc + 8 * i:x} {pt[3]}" for i, pt in enumerate(parts)))
        self.emit("    " + " ".join(pt[2] for pt in parts) + " " + " ".join(pt[4] for pt in parts))
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit("  rw [" + ", ".join(f"sv_mbRo F fR{k-1} {pt[2]}" for pt in parts) + f"] at D{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.pinned.add(f"D{k}")
        self.frame_after(k, [(oc, 32)], {})
        body = " ++ ".join(f"memBytes M0 ({pt[0]}) ({pt[1]})" for pt in parts)
        self.digest = (k, oc, f"sha256 ({body})")
        return k

    def digest_word(self):
        """The digest's first word, as a frame word fact."""
        kd, oc, ex = self.digest
        k = self.k
        val = f"le4 ({ex}) 0"
        if kd == k:
            pf = f"ld_digest D{k} (by decide)"
        else:
            pf = f"by rw [m{k}]; exact ld_digest D{kd} (by decide)"
        self.emit(f"  have w{k}_{oc:x} : {self.word_stmt(k, oc, ('U', val))} := {pf}")
        self.words[oc] = ("U", val)

    def esl(self, off, p, q, nl, hp, hq):
        """`<[u8]>::equal_same_length` of `nl` bytes at `p` and `q`; returns k.
        The result in `a0` is left to the caller."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_eslF", f"(nl := {nl})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"a0_{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    g{k-1}_10 g{k-1}_11 g{k-1}_12 {hp} {hq}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mbRo F fR{k-1} {hp}, sv_mbRo F fR{k-1} {hq}] at a0_{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.frame_after(k, [], {})
        return k

    def b64f(self, off, rc, oc, tc, nl, L):
        """`base64::decode_into` of the `nl` bytes at offset `tc` of the frame;
        returns k. The caller rewrites the input bytes and splits."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_b64fF", f"(rc := 0x{rc:X}) (oc := 0x{oc:X}) (tc := 0x{tc:X}) (nl := {nl}) (L := {L})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Bad{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (CK0.sv F fR{k-1}) s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, rc)} {self.reg_is(k - 1, 11, tc)} g{k-1}_12 {self.reg_is(k - 1, 13, oc)} g{k-1}_14")
        self.emit(f"    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k

    def ed(self, off, oc, pk, msg, ln, L, hsig, pk_in, msg_in, hlen, ha2):
        """`ed25519_verify` of the signature `L` at offset `oc`; returns k. The
        result in `a0` is left to the caller."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_edF", f"(oc := 0x{oc:X}) (len := {ln}) (L := {L}) (M0 := M0)",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"a0_{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} EE0 RS hiv fR{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    g{k-1}_10 g{k-1}_11 {ha2} {self.reg_is(k - 1, 13, oc)} (by decide) {hsig} {pk_in} {msg_in} {hlen}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.frame_after(k, [], {})
        return k

    def gt(self, off, oc, p, nl, inp, ha2):
        """`time::generalized_time` on the `nl` bytes at `p`, split on its answer:
        `None` reads the error flag at `oc + 0x60 - 0x60` with `lbu`, `beqz` not
        taken, `lbu s0`, and `j` to 0x2C60. Returns (k, the time's name)."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_gtF", f"(oc := 0x{oc:X}) (nl := {nl})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"Ok{k}", f"Er{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} g{k-1}_11 {ha2} (by decide) (by decide) {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at Ok{k} Er{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        ex = f"generalizedTime (memBytes M0 ({p}) ({nl}))"
        tt = f"tm{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with _ | {tt}")
        self.sc.append(("eq", ex, f"some {tt}", [tt], f"hr{k}"))
        self.fork(lambda sub: sub.gt_none(k, oc))
        self.emit(f"  obtain ⟨-, y0_{k}, y8_{k}, y12_{k}⟩ := Ok{k} {tt} hr{k}")
        self.frame_after(k, [(oc, 16)], {oc + 8: (f"BitVec.ofNat 32 ({tt} % 2 ^ 32)", f"y8_{k}"),
                                         oc + 12: (f"BitVec.ofNat 32 ({tt} / 2 ^ 32)", f"y12_{k}")},
                         {oc: ("(0 : BitVec 8)", f"y0_{k}")})
        return k, tt

    def gt_none(self, k, oc):
        """`gt`'s failing case at 0x28A0."""
        self.emit(f"  obtain ⟨y0_{k}, y1_{k}⟩ := Er{k} hr{k}")
        self.frame_after(k, [(oc, 16)], {}, {oc: ("(1 : BitVec 8)", f"y0_{k}"), oc + 1: ("(0x19 : BitVec 8)", f"y1_{k}")})
        self.load(0x28A0, "lbu")
        self.branch(0x28A4, False, f"by rw [g{self.k}_10, s{self.k}.zero]; decide")
        self.load(0x28A6, "lbu")
        self.jump(0x28AA)
        self.fail(self.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")

    def ds32(self, off, oc, dc, fail_tail):
        """`der::scalar::<32>` on the reader at `dc`, with the result at `oc`,
        split on its result. Returns k; the success case's bytes are `bs{k}`."""
        k = self.k = self.k + 1
        rp, rl, inp = self.reader(k - 1, dc)
        self.call_head(k, off, "sv_ds32F", f"(oc := 0x{oc:X}) (dc := 0x{dc:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"A{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} {self.reg_is(k - 1, 11, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {inp}] at A{k} R{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
        ex = f"derScalarOf 32 {L} ({rp}) (derElement 2 {L})"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with eb{k} | bs{k}")
        self.sc.append(("eq", ex, f".ok bs{k}", [f"bs{k}"], f"hr{k}"))
        self.fork(lambda sub: ds32_fail(sub, k, oc, dc, fail_tail))
        self.emit(f"  rw [hr{k}] at R{k}")
        self.emit(f"  obtain ⟨y0_{k}, yb_{k}⟩ := R{k}")
        te = f"te{k}"
        self.emit(f"  obtain ⟨{te}, hte{k}⟩ := derScalarOf_elem hr{k}")
        self.sc.append(("eq", f"derElement 2 {L}", f".ok {te}", [te], f"hte{k}"))
        self.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} {te} hte{k}")
        self.emit(f"  have q{k}_{oc + 1:x} : ∀ j, j < 32 → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{oc + 1:X} + j)) = "
                  f"BitVec.ofNat 8 ((bs{k}).getD j 0) := fun j hj => by rw [show 0x{oc + 1:X} + j = 0x{oc:X} + 1 + j by omega]; exact yb_{k} j hj")
        hl = f"BitVec.ofNat 32 ({te}.header + {te}.len)"
        self.frame_after(k, [(oc, 33), (dc + 8, 8)],
                         {dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")},
                         {oc: ("(0 : BitVec 8)", f"y0_{k}")})
        self.ranges[oc + 1] = (32, f"BitVec.ofNat 8 ((bs{k}).getD j 0)")
        self.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hte{k})"
        return k

    def word_of_bytes(self, e, x):
        """The word at offset `e` is `x`, from byte facts `x.extractLsb' (8 i) 8`."""
        k = self.k
        self.emit(f"  have w{k}_{e:x} : {self.word_stmt(k, e, ('U', x))} := ld_of_bytes b{k}_{e:x}")
        for i in (1, 2, 3):
            self.emit(f"    (by rw [show {fa(e)} + {i} = {fa(e + i)} by sv_addr]; exact b{k}_{e + i:x})")
        self.words[e] = ("U", x)
        for i in range(4):
            self.bytes.pop(e + i, None)

    def assemble_word(self, e, x):
        """The word at offset `e` is `x`, from the bytes `sb` stored of `x` and of
        `x` shifted right by 8, 16, and 24."""
        k = self.k
        self.emit(f"  have w{k}_{e:x} : {self.word_stmt(k, e, ('U', x))} := ld_of_shr_bytes b{k}_{e:x}")
        for i in (1, 2, 3):
            self.emit(f"    (by rw [show {fa(e)} + {i} = {fa(e + i)} by sv_addr]; exact b{k}_{e + i:x})")
        self.words[e] = ("U", x)
        for i in range(4):
            self.bytes.pop(e + i, None)


    def load_mem(self, off, val, eq, inp, al):
        """`lw` of a word outside the stack: `eq` says the word at the address is
        `val`, `inp` that its 4 bytes are outside the stack, and `al` that the
        address is aligned."""
        text, ln = INSTR[off]
        tk = tokens(text)
        rd, base, imm = reg_of(tk[2]), reg_of(tk[3]), int(tk[4], 16)
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: lw outside the stack")
        self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.lw E{k-1}.self sv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
        self.emit(f"    (by rw [g{k-1}_{base}]; exact {al})")
        self.st(k, off + ln)
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"(.single d{k})", f"fr{k}", f"V{k-1}.same m{k}")
        new = {}
        for r, v in sorted(self.regs.items()):
            if r == rd:
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [u{k}.regs, upd_ne (by decide) (by decide), g{k-1}_{r}]")
            new[r] = v
        self.emit(f"  have g{k}_{rd} : reg n{k} {rname(rd)} = {val} := by")
        self.emit(f"    rw [u{k}.regs]; simp +decide only [upd, ↓reduceIte]")
        self.emit(f"    rw [g{k-1}_{base}, sv_ld fR{k-1} {inp}, {eq}]")
        new[rd] = ("U", val)
        self.regs = new
        self.keep_frame(k, ("same",))
        self.end_step()

    # --- operations -------------------------------------------------------------

    def block(self, start, end, extra=None):
        """ALU instructions from `start` to `end`. `extra` maps a register to its
        value and a proof, from facts of the step before."""
        k = self.k = self.k + 1
        ins, off, vals, writes, unc = [], start, dict(self.regs), {}, {}
        vals[0] = ("C", 0)
        while off < end:
            text, ln = INSTR[off]
            ins.append(text)
            tk = tokens(text)
            if tk[0] == ".lui":
                rd = reg_of(tk[1]); v = ("C", int(tk[2], 16))
            elif tk[0] == ".aluImm" and tk[1] == ".add":
                rd = reg_of(tk[2]); src = vals.get(reg_of(tk[3])); v = add(src, ("C", int(tk[4], 16)))
                if src is not None and src[0] == "U" and v is not None and v != src:
                    unc[rd] = reg_of(tk[3])
            elif tk[0] == ".alu" and tk[1] == ".add":
                rd = reg_of(tk[2]); x, y = vals.get(reg_of(tk[3])), vals.get(reg_of(tk[4]))
                v = add(x, y)
                if x is not None and y is not None and x[0] == "U" and y[0] == "U":
                    unc[rd] = (reg_of(tk[3]), reg_of(tk[4]))
            elif tk[0] == ".aluImm" and tk[1] == ".and":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3]))
                v = ("C", x[1] & int(tk[4], 16)) if x is not None and x[0] == "C" else None
                if x is not None and x[0] == "U":
                    v = ("U", f"({lean_val(x)}) &&& BitVec.ofNat 32 0x{int(tk[4], 16):X}")
                    unc[rd] = reg_of(tk[3])
            elif tk[0] == ".aluImm" and tk[1] == ".srl":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3]))
                v = None
                if x is not None and x[0] == "U":
                    v = ("U", f"({lean_val(x)}) >>> {int(tk[4], 16)}")
                    unc[rd] = reg_of(tk[3])
            elif tk[0] == ".aluImm" and tk[1] == ".sll":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3]))
                v = ("C", (x[1] << int(tk[4], 16)) & 0xFFFFFFFF) if x is not None and x[0] == "C" else None
                if v is None and x is not None and self.generic_alu and start + ln == end:
                    v = ("U", f"aluEval .sll ({lean_val(x)}) (BitVec.ofNat 32 0x{int(tk[4], 16):X})")
                    unc[rd] = reg_of(tk[3])
            elif tk[0] == ".alu" and tk[1] == ".sub":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3])); y = vals.get(reg_of(tk[4]))
                v = ("U", f"({lean_val(x)}) - ({lean_val(y)})") if x is not None and y is not None and x[0] == "U" and y[0] == "U" else None
            elif tk[0] == ".alu" and tk[1] == ".and":
                rd = reg_of(tk[2]); x, y = vals.get(reg_of(tk[3])), vals.get(reg_of(tk[4]))
                v = ("U", f"({lean_val(x)}) &&& ({lean_val(y)})") if x is not None and y is not None else None
                if v is not None:
                    unc[rd] = (reg_of(tk[3]), reg_of(tk[4]))
            elif tk[0] == ".alu" and tk[1] == ".or":
                rd = reg_of(tk[2]); x, y = vals.get(reg_of(tk[3])), vals.get(reg_of(tk[4]))
                v = ("U", f"({lean_val(x)}) ||| ({lean_val(y)})") if x is not None and y is not None else None
                if v is not None:
                    unc[rd] = (reg_of(tk[3]), reg_of(tk[4]))
            elif tk[0] == ".aluImm" and tk[1] == ".xor":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3]))
                v = ("C", x[1] ^ int(tk[4], 16)) if x is not None and x[0] == "C" else None
                if v is None and x is not None and self.generic_alu and start + ln == end:
                    v = ("U", f"aluEval .xor ({lean_val(x)}) (BitVec.ofNat 32 0x{int(tk[4], 16):X})")
                    unc[rd] = reg_of(tk[3])
            elif tk[0] in (".aluImm", ".alu"):
                rd = reg_of(tk[2]); v = None
                if self.generic_alu and start + ln == end:
                    xs = reg_of(tk[3])
                    ys = reg_of(tk[4]) if tk[0] == ".alu" else None
                    x = vals.get(xs)
                    y = vals.get(ys) if ys is not None else ("C", int(tk[4], 16))
                    if x is not None and y is not None:
                        v = ("U", f"aluEval {tk[1]} ({lean_val(x)}) ({lean_val(y)})")
                        srcs = tuple(q for q in (xs, ys) if q is not None and q != 0)
                        if srcs:
                            unc[rd] = srcs
            else:
                raise ValueError(text)
            vals[rd] = v
            writes[rd] = v
            off += ln
        blk = f"sv{self.name}{start:x}"
        if any(b[0] == blk and b[2] != end for b in self.blocks):
            blk += f"_{end:x}"
        if all(b[0] != blk for b in self.blocks):
            self.blocks.append((blk, start, end, ins))
        self.emit(f"  -- 0x{start:X}")
        self.emit(f"  obtain ⟨n{k}, c{k}, u{k}⟩ := s{k-1}.block {blk} E{k-1}.self {blk}_end")
        self.emit(f"    ⟨{', '.join(['trivial'] * (len(ins) + 1))}⟩")
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.st(k, end)
        self.emit(f"  have rb{k} : ∀ q, reg n{k} q = (runBlock {blk} (n{k-1}.mem, reg n{k-1})).2 q := fun q => by rw [u{k}.regs]")
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.same m{k}")
        new = {}
        prev = ", ".join([f"g{k-1}_{r}" for r in sorted(self.regs)] + [f"s{k-1}.zero"])
        for r, v in sorted(self.regs.items()):
            if r in writes:
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by")
            self.emit(f"    rw [rb{k}, runBlock_reg _ _ _ {rname(r)} s{k-1}.zero (by decide), g{k-1}_{r}]")
            new[r] = v
        for r, v in sorted(writes.items()):
            if v is None or r in (extra or {}):
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by")
            if r in unc and len(ins) == 1:
                srcs = unc[r] if isinstance(unc[r], tuple) else (unc[r],)
                if self.generic_alu:
                    fw = ", ".join(f"g{k-1}_{q}" for q in dict.fromkeys(srcs))
                    self.emit(f"    rw [rb{k}]; simp +decide only [runBlock, BInstr.run, {blk}, upd, ↓reduceIte]; rw [{fw}] <;> rfl")
                else:
                    self.emit(f"    rw [rb{k}" + "".join(f", ← g{k-1}_{q}" for q in srcs) + "]; rfl")
                new[r] = v
                continue
            self.emit(f"    rw [rb{k}]; simp +decide only [runBlock, BInstr.run, {blk}, upd, ↓reduceIte, aluEval]")
            self.emit(f"    all_goals (try simp only [{prev}])")
            if any(tokens(t)[1] == ".sll" for t in ins if tokens(t)[0] == ".aluImm"):
                self.emit("    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])")
            self.emit(f"    all_goals first | with_reducible rfl | sv_addr | decide")
            new[r] = v
        for r, (v, pf) in (extra or {}).items():
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {v} := by")
            self.emit(f"    {pf.format(k=k, p=k - 1)}")
            new[r] = ("U", v)
        self.regs = new
        self.keep_frame(k, ("same",))
        self.end_step()

    def load(self, off, kind):
        """`lw` or `lbu` of a word or byte of the frame whose value the facts give."""
        text, ln = INSTR[off]
        tk = tokens(text)
        rd, base, imm = reg_of(tk[2]), reg_of(tk[3]), int(tk[4], 16)
        bv = self.regs[base]
        assert bv[0] == "S", text
        e = (bv[1] + s32(imm)) & 0xFFFFFFFF
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: {kind}")
        if kind == "lw":
            self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.lw E{k-1}.self sv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
            self.emit(f"    (by rw [g{k-1}_{base}, show {lean_val(bv)} + 0x{imm:X} = {fa(e)} by sv_addr]; exact sv_al F (by decide) (by decide))")
            val = self.words[e]
            vstr = lean_val(val)
            fact = f"w{k-1}_{e:x}"
        else:
            if e not in self.bytes and (e - e % 4) not in self.words:
                for s0, (n, tmpl) in self.ranges.items():
                    if s0 <= e < s0 + n:
                        val = re.sub(r"\bj\b", f"{e - s0}", tmpl)
                        self.emit(f"  have b{k-1}_{e:x} : {self.byte_stmt(k - 1, e, val)} := q{k-1}_{s0:x} {e - s0} (by decide)")
                        self.bytes[e] = val
                        break
            self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.lbu E{k-1}.self sv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
            if e not in self.bytes:
                self.byte_from_word(k - 1, e)
            vstr = f"({self.bytes[e]}).zeroExtend 32"
            val = ("Z", vstr, self.bytes[e])
            fact = f"b{k-1}_{e:x}"
        self.st(k, off + ln)
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"(.single d{k})", f"fr{k}", f"V{k-1}.same m{k}")
        new = {}
        for r, v in sorted(self.regs.items()):
            if r == rd:
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [u{k}.regs, upd_ne (by decide) (by decide), g{k-1}_{r}]")
            new[r] = v
        self.emit(f"  have g{k}_{rd} : reg n{k} {rname(rd)} = {vstr} := by")
        self.emit(f"    rw [u{k}.regs]; simp +decide only [upd, ↓reduceIte]")
        self.emit(f"    rw [g{k-1}_{base}, show {lean_val(bv)} + 0x{imm:X} = {fa(e)} by sv_addr, {fact}]")
        new[rd] = val if kind == "lw" else ("U", vstr, self.bytes[e])
        self.regs = new
        self.keep_frame(k, ("same",))
        self.end_step()

    def byte_from_word(self, k, e):
        """A byte fact for offset `e` at state k, from the word that holds it."""
        base = e - (e % 4)
        i = e % 4
        v = lean_val(self.words[base])
        b = f"({v}).extractLsb' {8 * i} 8"
        sel = ["h.1", "h.2.1", "h.2.2.1", "h.2.2.2"][i]
        addr = fa(base) + ("" if i == 0 else f" + {i}")
        self.emit(f"  have b{k}_{e:x} : {self.byte_stmt(k, e, b)} := by")
        self.emit(f"    have h := byte_of_ld w{k}_{base:x}")
        self.emit(f"    rw [show {fa(e)} = {addr} by sv_addr]; exact {sel}")
        self.bytes[e] = b

    def store(self, off, kind):
        text, ln = INSTR[off]
        tk = tokens(text)
        base, src, imm = reg_of(tk[2]), reg_of(tk[3]), int(tk[4], 16)
        bv = self.regs[base]
        assert bv[0] == "S", text
        e = (bv[1] + s32(imm)) & 0xFFFFFFFF
        k = self.k = self.k + 1
        w = 4 if kind == "sw" else 1
        wrapper = "sv_sw" if kind == "sw" else "sv_sb"
        self.emit(f"  -- 0x{off:X}: {kind}")
        extra = " (by decide)" if kind == "sw" else ""
        self.emit(f"  obtain ⟨n{k}, d{k}, s{k}, fr{k}, K{k}, W{k}, rg{k}⟩ := {wrapper} F E{k-1} s{k-1} sv_at_{off:x} (off' := 0x{off + ln:X}) (c := 0x{e:X})")
        self.emit(f"    (by decide) (by rw [g{k-1}_{base}]; sv_addr) (by decide){extra}")
        self.common(k, f"d{k}", f"fr{k}", f"V{k-1}.keep K{k} (by decide)")
        sv = self.regs.get(src) if src != 0 else ("C", 0)
        srcfact = f"g{k-1}_{src}" if src != 0 else f"s{k-1}.zero"
        if sv is None:
            ww, wb = {}, {}
        elif kind == "sw":
            ww = {e: (sv, f"by rw [W{k}, {srcfact}]" + ("; rfl" if src == 0 else ""))}
            wb = {}
        else:
            if sv[0] == "U" and len(sv) == 3:
                ww, wb = {}, {e: (sv[2], f"by rw [W{k}, {srcfact}, lbu_low]")}
            else:
                ww, wb = {}, {e: (f"({lean_val(sv)}).extractLsb' 0 8", f"by rw [W{k}, {srcfact}]" + ("; rfl" if src == 0 else ""))}
        self.keep_regs(k, range(32), lambda r: f"rg{k} {rname(r)}")
        self.keep_frame(k, ("K", e, w), ww, wb)
        self.end_step()

    def mc(self, off, dst, src, N):
        """`memcpy` of `N` bytes from offset `src` of the frame to `dst`."""
        k = self.k
        ww, wb = {}, {}
        for e, v in self.words.items():
            if src <= e and e + 4 <= src + N:
                ne = dst + (e - src)
                ww[ne] = (v, "by\n" + "\n".join([
                    f"    rw [← w{k}_{e:x}]",
                    "    exact ld_cp fun q hq => by",
                    f"      have := X{k + 1} (0x{e - src:X} + q) (by omega)",
                    f"      rwa [show 0x{dst:X} + (0x{e - src:X} + q) = 0x{ne:X} + q by omega,",
                    f"        show 0x{src:X} + (0x{e - src:X} + q) = 0x{e:X} + q by omega] at this"]))
        for j in range(N):
            e = src + j
            ne = dst + j
            if any(ne in range(w0, w0 + 4) for w0 in ww):
                continue
            if e not in self.bytes and (e - e % 4) in self.words:
                self.byte_from_word(k, e)
            if e in self.bytes:
                wb[ne] = (self.bytes[e], f"by rw [show 0x{ne:X} = 0x{dst:X} + 0x{j:X} from rfl, X{k + 1} 0x{j:X} (by decide)]; exact b{k}_{e:x}")
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: memcpy")
        self.emit(f"  obtain ⟨n{k}, P{k}, K{k}, X{k}⟩ := sv_mc (c := 0x{dst:X}) (d := 0x{src:X}) (N := 0x{N:X}) F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x}")
        self.emit(f"    (by decide) (by decide) g{k-1}_2 {self.reg_is(k-1, 10, dst)} {self.reg_is(k-1, 11, src)} g{k-1}_12")
        self.emit(f"    (by decide) (by decide) (by decide)")
        self.emit(f"  have s{k} := P{k}.st")
        self.emit(f"  have fr{k} := P{k}.fr")
        self.common(k, f"P{k}.steps", f"fr{k}", f"V{k-1}.keep K{k} (by decide)")
        self.keep_regs(k, CALL_KEEP, lambda r: f"P{k}.regs {rname(r)} (by decide)")
        moved = {}
        for s0, (n, tmpl) in sorted(self.ranges.items()):
            lo, hi = max(s0, src), min(s0 + n, src + N)
            if lo < hi:
                d, o = lo - s0, lo - src
                moved[dst + o] = (hi - lo, re.sub(r"\bj\b", f"({d} + j)", tmpl) if d else tmpl, s0, d, o)
        macc = {}
        for d0, (n, v) in sorted(self.acc.items()):
            if src <= d0 and d0 + 4 * n <= src + N:
                macc[dst + d0 - src] = (n, v, d0)
        self.keep_frame(k, ("K", dst, N), ww, wb)
        for nd, (n, v, d0) in sorted(macc.items()):
            o = d0 - src
            self.emit(f"  have a{k}_{nd:x} : {self.acc_stmt(k, nd, n, v)} := (accV_S {n} fun q hq => by")
            self.emit(f"    rw [show 0x{nd:X} + q = 0x{dst:X} + (0x{o:X} + q) by omega, X{k} (0x{o:X} + q) (by omega),")
            self.emit(f"      show 0x{src:X} + (0x{o:X} + q) = 0x{d0:X} + q by omega]).trans a{k-1}_{d0:x}")
            self.acc[nd] = (n, v)
        for ns, (n, tmpl, s0, d, o) in sorted(moved.items()):
            self.emit(f"  have q{k}_{ns:x} : ∀ j, j < {n} → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{ns:X} + j)) = {tmpl} := fun j hj => by")
            dj = f"({d} + j)" if d else "j"
            self.emit(f"    rw [show 0x{ns:X} + j = 0x{dst:X} + (0x{o:X} + j) by omega, X{k} (0x{o:X} + j) (by omega),")
            self.emit(f"      show 0x{src:X} + (0x{o:X} + j) = 0x{s0:X} + {dj} by omega]; exact q{k-1}_{s0:x} {dj} (by omega)")
            self.ranges[ns] = (n, tmpl)
        self.end_step()

    def mcIn(self, off, dst, p, N, inp):
        """`memcpy` of `N` bytes at `p` outside the stack, whose `SvIn` is `inp`,
        to offset `dst` of the frame."""
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: memcpy from the bundle")
        self.emit(f"  obtain ⟨n{k}, P{k}, K{k}, X{k}⟩ := sv_mcIn (c := 0x{dst:X}) (N := 0x{N:X}) F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x}")
        self.emit(f"    (by decide) (by decide) g{k-1}_2 {self.reg_is(k-1, 10, dst)} g{k-1}_11 g{k-1}_12 (by decide) {inp}")
        self.emit(f"  have s{k} := P{k}.st")
        self.emit(f"  have fr{k} := P{k}.fr")
        self.common(k, f"P{k}.steps", f"fr{k}", f"V{k-1}.keep K{k} (by decide)")
        self.keep_regs(k, CALL_KEEP, lambda r: f"P{k}.regs {rname(r)} (by decide)")
        self.keep_frame(k, ("K", dst, N), {}, {})
        tmpl = f"M0 (({p}) + BitVec.ofNat 32 j)"
        self.emit(f"  have q{k}_{dst:x} : ∀ j, j < {N} → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{dst:X} + j)) = {tmpl} :=")
        self.emit(f"    fun j hj => (X{k} j hj).trans (fR{k-1} _ ({inp}.r hj))")
        self.ranges[dst] = (N, tmpl)
        self.end_step()

    def mcRo(self, off, dst, p, N, inp):
        """`memcpy` of `N` bytes at `p` in the bundle or the image's constants,
        whose `SvRo2` is `inp`, to offset `dst` of the frame."""
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: memcpy from outside the stack")
        self.emit(f"  obtain ⟨n{k}, P{k}, K{k}, X{k}⟩ := sv_mcRo2 (c := 0x{dst:X}) (N := 0x{N:X}) F RS E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x}")
        self.emit(f"    (by decide) (by decide) g{k-1}_2 {self.reg_is(k-1, 10, dst)} g{k-1}_11 g{k-1}_12 (by decide) {inp}")
        self.emit(f"  have s{k} := P{k}.st")
        self.emit(f"  have fr{k} := P{k}.fr")
        self.common(k, f"P{k}.steps", f"fr{k}", f"V{k-1}.keep K{k} (by decide)")
        self.keep_regs(k, CALL_KEEP, lambda r: f"P{k}.regs {rname(r)} (by decide)")
        self.keep_frame(k, ("K", dst, N), {}, {})
        tmpl = f"M0 (({p}) + BitVec.ofNat 32 j)"
        self.emit(f"  have q{k}_{dst:x} : ∀ j, j < {N} → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{dst:X} + j)) = {tmpl} :=")
        self.emit(f"    fun j hj => (X{k} j hj).trans (fR{k-1} _ (SvRo2.r RS {inp} hj))")
        self.ranges[dst] = (N, tmpl)
        self.end_step()

    def hinit(self):
        """The hasher at 0x420 holds nothing."""
        k = self.k
        self.emit(f"  have H{k} := hasher_init_f b{k}_45f q{k}_460 S2.iv w{k}_480 w{k}_484")
        self.pinned.add(f"H{k}")
        self.hasher = (k, "[]", [])

    def carry_hasher(self):
        kh, msg, bl = self.hasher
        k = self.k
        if kh == k:
            return
        self.emit(f"  have H{k} : HasherAt n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) ({msg}) := by rw [m{k}]; exact H{kh}")
        self.pinned.add(f"H{k}")
        self.hasher = (k, msg, bl)

    def hlen_proof(self, extra):
        kh, msg, bl = self.hasher
        facts = "; ".join(bl)
        return (f"(by {facts + '; ' if facts else ''}simp only [List.length_append, List.length_nil, memBytes_length]{' at *' if False else ''}; omega)"
                if True else "")

    def upd(self, off, D, nl, inp, hn, bound):
        """`Sha256::update` of the `nl` bytes at `D` into the hasher at 0x420."""
        self.carry_hasher()
        kh, msg, bl = self.hasher
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_updF", f"(hc := 0x420) (nl := {nl}) (msg := {msg})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"H{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (S2.sv F KS fR{k-1}) KS RS s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, 0x420)} g{k-1}_11 g{k-1}_12 (by decide) (by decide) {inp} H{kh} {hn}")
        pre = [x for x in bl + [bound] if x]
        self.emit(f"    (by {'; '.join(pre) + '; ' if pre else ''}simp only [List.length_append, List.length_nil, memBytes_length]; omega)")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mbRo2 RS fR{k-1} {inp}] at H{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.pinned.add(f"H{k}")
        self.frame_after(k, [(0x420, 0x68)], {})
        self.hasher = (k, f"{msg} ++ memBytes M0 ({D}) ({nl})", bl)

    def b64e(self, off, D, nl, inp, ha1, bound):
        """`base64::encode_to` of the `nl` bytes at `D` into the hasher at 0x420."""
        self.carry_hasher()
        kh, msg, bl = self.hasher
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_b64eF", f"(hc := 0x420) (nl := {nl}) (msg := {msg})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"H{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (S2.sv F KS fR{k-1}) (RK0.sv F fR{k-1}) KS RS s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    g{k-1}_10 {ha1} {self.reg_is(k - 1, 12, 0x420)} (by decide) (by decide) {inp} H{kh}")
        pre = [x for x in bl + [bound] if x]
        self.emit(f"    (by {'; '.join(pre) + '; ' if pre else ''}simp only [List.length_append, List.length_nil, memBytes_length]; omega)")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mbRo2 RS fR{k-1} {inp}] at H{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.pinned.add(f"H{k}")
        self.frame_after(k, [(0x420, 0x68)], {})
        piece = f"memBytes M0 ({D}) ({nl})"
        nb = bl + [f"have := b64_len_le ({piece}); rw [memBytes_length] at this"]
        self.hasher = (k, f"{msg} ++ base64Encode ({piece})", nb)

    def fin(self, off, oc):
        """`Sha256::finish` of the hasher at 0x420 into offset `oc`."""
        self.carry_hasher()
        kh, msg, bl = self.hasher
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_finF", f"(hc := 0x420) (oc := 0x{oc:X}) (msg := {msg})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"D{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (S2.sv F KS fR{k-1}) (RK0.sv F fR{k-1}) KS s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} {self.reg_is(k - 1, 11, 0x420)} (by decide) (by decide) H{kh}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        self.pinned.add(f"D{k}")
        self.frame_after(k, [(oc, 32)], {})
        self.digest = (k, oc, f"sha256 ({msg})")

    def rfi(self, off, pp, np, inp, ha7):
        """`merkle::root_from_inclusion` with the digest at 0x1380 as the leaf
        hash and the result at 0x420; returns k and the spec's value."""
        kd, ocd, lh = self.digest
        assert ocd == 0x1380 and kd == self.k
        k = self.k = self.k + 1
        a = [lean_val(self.regs[r]) for r in (11, 12, 13, 14)]
        self.call_head(k, off, "sv_rfiF", f"(oc := 0x420) (lc := 0x1380) (np := {np})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"K{k}", f"R{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (S2.sv F KS fR{k-1}) (RK0.sv F fR{k-1}) KS RS s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, 0x420)} {self.reg_is(k - 1, 15, 0x1380)} g{k-1}_16 {ha7} (by decide) (by decide) {inp}")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [g{k-1}_11, g{k-1}_12, g{k-1}_13, g{k-1}_14, D{kd}, sv_mbRo2 RS fR{k-1} {inp}] at R{k}")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k, f"rootFromInclusion (pair64 ({a[0]}) ({a[1]})) (pair64 ({a[2]}) ({a[3]})) ({lh}) (memBytes M0 ({pp}) ({np}))"

    def a32eq(self, off, oc, oc2, post=()):
        """`<[u8; 32]>::eq` of the frame's bytes at `oc` and `oc2`; returns k.
        The result in `a0` is left to the caller. `post` gets k and returns
        lines that use the facts before the call."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_a32eqF", f"(oc := 0x{oc:X}) (oc2 := 0x{oc2:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"a0_{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, oc)} {self.reg_is(k - 1, 11, oc2)} (by decide) (by decide)")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        for line in (post(k) if post else []):
            self.emit(line)
        self.frame_after(k, [], {})
        return k

    def pure(self, off, wrapper, named, args, post=None):
        """A call through `wrapper` that leaves memory alone and returns its
        result in `a0`; returns k. The result is left to the caller. `post`
        gets k and returns lines that use the facts before the call."""
        k = self.k = self.k + 1
        self.call_head(k, off, wrapper, named, [f"c{k}", f"s{k}", f"rk{k}", f"a0_{k}", f"m{k}"])
        self.emit(f"    {args}")
        for line in (post(k) if post else []):
            self.emit(line)
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.same m{k}")
        self.keep_regs(k, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.keep_frame(k, ("same",))
        self.end_step()
        return k

    def isr(self, off, cx, y, post=None):
        """`ecdsa::in_scalar_range` of the 32 bytes at offset `cx` and at `y`."""
        k = self.k + 1
        return self.pure(off, "sv_isrF", "", f"E{k-1} (EC0.sv F fR{k-1}) s{k-1} sv_at_{off:x} sv_at_{off + 4:x} "
                         f"(by decide) (by decide) {self.reg_is(k - 1, 10, cx)} g{k-1}_11 g{k-1}_12 g{k-1}_13", post)

    def branch(self, off, taken, why):
        """A branch whose direction `why` proves: a term for `reg == reg` or its negation."""
        text, ln = INSTR[off]
        tk = tokens(text)
        tgt = off + s32(int(tk[4], 16)) if taken else off + ln
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: branch, {'taken' if taken else 'not taken'}")
        self.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.{'taken' if taken else 'notTaken'} E{k-1}.self 0x{tgt:X} sv_at_{off:x}")
        self.emit(f"    (by decide) ({why})")
        self.st(k, tgt)
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.emit(f"  have fr{k} : ∀ x, SvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.common(k, f"(.single d{k})", f"fr{k}", f"V{k-1}.same m{k}")
        self.keep_regs(k, range(32), lambda r: f"u{k}.regs")
        self.keep_frame(k, ("same",))
        self.end_step()
        return tgt

    def fail(self, why_not, exit_lemma="sv_fail"):
        """Close the failing case at 0x966 (or, with `exit_lemma`, 0xEE4 or
        0x2A82) with `why_not`, a proof that the stage's checks failed."""
        k = self.k
        self.emit(f"  exact .inl ⟨({why_not}), {exit_lemma} F E{k} s{k} t{k} (fun x hx => (fR{k} x hx).trans (fM x hx).symm) V{k} hret g{k}_2 g{k}_18 hO g{k}_3 g{k}_4⟩")

    # --- calls through SvDer ----------------------------------------------------

    def seq(self, off, oc, dc, bytes_name, rp, rl):
        """`Der::sequence`, split on its result. Returns the name of the `DerTlv`."""
        k = self.k = self.k + 1
        t = f"t{k}"
        self.emit(f"  -- 0x{off:X}: Der::sequence")
        self.emit(f"  obtain ⟨n{k}, c{k}, s{k}, sp{k}, rk{k}, K{k}, Ok{k}, Er{k}, fr{k}⟩ := sv_seqF (oc := 0x{oc:X}) (dc := 0x{dc:X})")
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k-1, 10, oc)} {self.reg_is(k-1, 11, dc)} (by decide) (by decide) (by decide) (by decide)")
        self.emit(f"    (by decide) w{k-1}_{dc + 8:x} w{k-1}_{dc + 12:x} {bytes_name}_in")
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.emit(f"  rw [sv_mb fR{k-1} {bytes_name}_in] at Ok{k} Er{k}")
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        return k

    def conclusion(self, off, keep_regs, keep_words, keep_bytes, wit):
        k = self.k
        conj = ["Steps n0 n'", f"St n'.mem SV n' 0x{off:X} (reg n')", "SvCode n'.mem", "SvSaves B n'.mem v",
                "(∀ x, SvR B x → n'.mem x = M0 x)"]
        terms = [f"t{k}", f"s{k}", f"E{k}", f"V{k}", f"fR{k}"]
        for r, v in sorted(self.regs.items()):
            if r not in keep_regs:
                continue
            conj.append(f"reg n' {rname(r)} = {lean_val(v)}")
            terms.append(f"g{k}_{r}")
        for e, v in sorted(self.words.items()):
            if e not in keep_words:
                continue
            conj.append(f"memLoad32 n'.mem ({fa(e)}) = {lean_val(v)}")
            terms.append(f"w{k}_{e:x}")
        for e, v in sorted(self.bytes.items()):
            if e not in keep_bytes:
                continue
            conj.append(f"n'.mem ({fa(e)}) = {v}")
            terms.append(f"b{k}_{e:x}")
        for s, (n, tmpl) in sorted(self.ranges.items()):
            conj.append(f"(∀ j, j < {n} → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{s:X} + j)) = {tmpl})")
            terms.append(f"q{k}_{s:x}")
        for d, (n, v) in sorted(self.acc.items()):
            conj.append(f"accV n'.mem ({fa(d)}) {n} = {v}")
            terms.append(f"a{k}_{d:x}")
        for c, t in self.extra:
            conj.append(c)
            terms.append(t)
        return conj, terms

    def block_defs(self):
        lines = []
        for blk, start, end, ins in self.blocks:
            lines.append(f"def {blk} : List BInstr :=")
            bi = [i.replace(".load .lw ", ".lw ").replace(".store .sw ", ".sw ") for i in ins]
            lines.append("  [" + ", ".join(bi) + "]")
            lines.append("set_option maxRecDepth 100000 in")
            lines.append(f"theorem {blk}_end : blockEnd sigstoreVerifyCode 0x{start:X} {blk} = some 0x{end:X} := by decide")
            lines.append("")
        return lines


HEADER = """import {imp}

/-!
# `sigstore::verify`: {title}

{doc}
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
"""


def stage_l1():
    """From the call to `Der::sequence` at 0x72 to the call to `Der::element` at 0xD0."""
    g = Gen("L1")
    g.regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
              10: ("S", 0xA20), 11: ("S", 0x2E0), 27: ("S", 0xA20), 21: ("U", "lp"), 26: ("U", "ll"),
              19: ("U", "bp"), 25: ("U", "rootp"), 22: ("U", "dg")}
    g.words = {e: ("U", v) for e, v in {0x2E0: "lp", 0x2E4: "ll", 0x2E8: "lp", 0x2EC: "ll"}.items()}
    params = []
    for r, v in sorted(g.regs.items()):
        if r in (3, 4):
            continue
        params.append(f"(g0_{r} : reg n0 {rname(r)} = {lean_val(v)})")
    for e, v in sorted(g.words.items()):
        params.append(f"(w0_{e:x} : memLoad32 n0.mem ({fa(e)}) = {lean_val(v)})")
    params.append("(lc_in : SvIn B lp ll.toNat)")
    g.emit("  have t0 : Steps n0 n0 := .refl n0")
    g.emit("  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM")
    g.emit("  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl")
    g.emit("  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl")
    der = "(memBytes M0 lp ll.toNat)"
    k = g.seq(0x72, 0xA20, 0x2E0, "lc", "lp", "ll")
    t = f"tl{k}"
    rest = f"ll - BitVec.ofNat 32 ({t}.header + {t}.len)"
    sc = f"∃ t, derElement 0x30 {der} = .ok t ∧ ll - BitVec.ofNat 32 (t.header + t.len) = 0"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, derElement 0x30 {der} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with er | {t}")

    def fail1(sub):
        kk = sub.k
        sub.emit(f"  obtain ⟨z{kk}, -⟩ := Er{kk} er hr{kk}")
        sub.keep_frame_L(kk, [(0xA20, 16), (0x2E8, 8)])
        sub.words[0xA20] = ("C", 0)
        sub.emit(f"  have w{kk}_a20 : {sub.word_stmt(kk, 0xA20, ('C', 0))} := z{kk}")
        sub.end_step()
        sub.load(0x7A, "lw")
        sub.load_any(0x7E)
        sub.branch(0x82, True, f"by rw [g{sub.k}_8, s{sub.k}.zero]; rfl")
        sub.fail(f"fun ⟨t', h', _⟩ => by rw [hr{k}] at h'; cases h'")
    g.fork(fail1)
    g.emit(f"  obtain ⟨o0_{k}, o4_{k}, o8_{k}, o12_{k}, d8_{k}, d12_{k}⟩ := Ok{k} {t} hr{k}")
    g.keep_frame_L(k, [(0xA20, 16), (0x2E8, 8)])
    hd = f"lp + BitVec.ofNat 32 {t}.header"
    for e, v, h in ((0xA20, hd, "o0"), (0xA24, f"BitVec.ofNat 32 {t}.len", "o4"), (0xA28, hd, "o8"),
                    (0xA2C, f"BitVec.ofNat 32 {t}.len", "o12"), (0x2E8, f"lp + BitVec.ofNat 32 ({t}.header + {t}.len)", "d8"),
                    (0x2EC, rest, "d12")):
        g.words[e] = ("U", v)
        g.emit(f"  have w{k}_{e:x} : {g.word_stmt(k, e, ('U', v))} := {h}_{k}")
    g.end_step()
    g.load(0x7A, "lw")
    g.load(0x7E, "lbu")
    g.branch(0x82, False, f"by rw [g{g.k}_8, s{g.k}.zero]; exact br_beq_f (lc_in.ok_ne hr{k})")
    g.block(0x86, 0xA2)
    g.mc(0xA2, 0x158D, 0xA25, 0xB)
    g.load(0xAA, "lw")
    g.store(0xAE, "sw")
    g.store(0xB2, "sb")
    g.block(0xB6, 0xB8)
    kz = g.k
    g.emit(f"  by_cases hz_{kz} : {rest} = 0")
    rest_k = kz

    def fail2(sub):
        sub.emit("  -- the reader has bytes left")
        sub.branch(0xB8, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t hz_{rest_k}")
        sub.fail(f"fun ⟨t', h', hz'⟩ => by rw [hr{k}] at h'; cases h'; exact hz_{rest_k} hz'")
    # The failing case is the second one of `by_cases`; swap them.
    g.emit("  rotate_left")
    g.fork(fail2)
    g.branch(0xB8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f hz_{rest_k}")
    g.block(0xBC, 0xD0)
    keep_regs = [2, 3, 4, 10, 11, 12, 18, 19, 21, 22, 25, 26, 27]
    conj, terms = g.conclusion(0xD0, keep_regs, set(g.words), set(g.bytes), [])
    stmt = (f"(¬ ({sc}) ∧ SvErrRet B out v n0) ∨\n    (∃ t, derElement 0x30 {der} = .ok t ∧ "
            f"ll - BitVec.ofNat 32 (t.header + t.len) = 0 ∧\n      ∃ n', " + " ∧\n        ".join(c.replace(t, "t") for c in conj) + ")")
    proof = f"  exact .inr ⟨{t}, hr{k}, hz_{rest_k}, n{g.k}, " + ", ".join(terms) + "⟩"
    info = {"name": "sv_l1", "title": "the certificate", "doc": "From the call to `Der::sequence` over the leaf "
            "certificate at 0x72 to the call to `Der::element` for the `tbsCertificate` at 0xD0: the "
            "certificate is one `SEQUENCE` that fills the bytes.",
            "params": params, "stmt": stmt, "proof": proof, "import": "C3BootProofs.Proofs.SvCongr"}
    return g, info



def start(g, regs, words, slices):
    """Sets the stage's starting facts and returns its hypotheses."""
    g.regs = dict(regs)
    g.words = {e: ("U", v) if isinstance(v, str) else v for e, v in words.items()}
    params = []
    for r, v in sorted(g.regs.items()):
        if r in (3, 4):
            continue
        params.append(f"(g0_{r} : reg n0 {rname(r)} = {lean_val(v)})")
    for e, v in sorted(g.words.items()):
        params.append(f"(w0_{e:x} : memLoad32 n0.mem ({fa(e)}) = {lean_val(v)})")
    for (rp, rl), name in slices.items():
        params.append(f"({name} : SvIn B ({rp}) ({rl}).toNat)")
        g.slices[(rp, rl)] = name
    g.emit("  have t0 : Steps n0 n0 := .refl n0")
    g.emit("  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM")
    g.emit("  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl")
    g.emit("  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl")
    return params


def finish(g, off, keep_regs, keep_words=None, keep_bytes=None):
    conj, terms = g.conclusion(off, keep_regs, keep_words if keep_words is not None else set(g.words),
                               keep_bytes if keep_bytes is not None else set(g.bytes), [])
    names = {}
    for c in g.sc:
        if c[0] == "eq":
            for b in c[3]:
                names[b] = b.rstrip("0123456789").rstrip("_") + "_" + b[len(b.rstrip("0123456789")):]
    body = "∃ n', " + " ∧\n        ".join(conj)
    stmt = (f"(¬ ({g.sc_prop()}) ∧ SvErrRet B out v n0) ∨\n    (" + g.sc_ok(body) + ")")
    proof = "  exact .inr ⟨" + ", ".join(g.sc_terms() + [f"n{g.k}"] + terms) + "⟩"
    for tag, sub in g.exits:
        assert sub.sc_prop() == g.sc_prop(), (tag, sub.sc_prop(), g.sc_prop())
        sconj, sterms = sub.conclusion(off, keep_regs, keep_words if keep_words is not None else set(g.words),
                                       keep_bytes if keep_bytes is not None else set(g.bytes), [])
        assert sconj == conj, (tag, set(sconj) ^ set(conj))
        line = "exact .inr ⟨" + ", ".join(sub.sc_terms() + [f"n{sub.k}"] + sterms) + "⟩"
        g.out = [l.replace(tag, line) for l in g.out]
    return stmt, proof


def lw_branch_fail(off_lw, off_br, reg):
    """The failing tail after a reader stored a null address: `lw`, `beqz` to 0x962, `lbu`."""
    def tail(sub):
        sub.load(off_lw, "lw")
        sub.branch(off_br, True, f"by rw [g{sub.k}_{reg}, s{sub.k}.zero]; rfl")
        sub.load_any(0x962)
    return tail


def stage_l2():
    """From the call to `Der::element` for the `tbsCertificate` at 0xD0 on."""
    g = Gen("L2")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            10: ("S", 0xA20), 11: ("S", 0x1588), 12: ("C", 0x30), 27: ("S", 0xA20), 21: ("U", "lp"),
            26: ("U", "ll"), 19: ("U", "bp"), 25: ("U", "rootp"), 22: ("U", "dg")}
    params = start(g, regs, {0x1590: "cp", 0x1594: "cl"}, {("cp", "cl"): "cc_in"})
    k, ex, rd = g.elem(0xD0, 0xA20, 0x1588, 0x30)
    t = g.elem_split(k, ex, 0xA20, 0x1588, rd, lw_branch_fail(0xD8, 0xDC, 24))
    g.load(0xD8, "lw")
    g.branch(0xDC, False, f"by rw [g{g.k}_24, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    for o in (0xE0, 0xE4, 0xE8):
        g.load(o, "lw")
    g.block(0xEC, 0x100)
    k, ex, rd = g.elem(0x100, 0xA20, 0x1588, 0x30)
    t = g.elem_split(k, ex, 0xA20, 0x1588, rd, lw_branch_fail(0x108, 0x10C, 10))
    g.load(0x108, "lw")
    g.branch(0x10C, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    g.store(0x110, "sw")
    g.store(0x112, "sw")
    g.load(0x114, "lw")
    g.load(0x118, "lw")
    g.block(0x11C, 0x12C)
    k = g.bits(0x12C, 0xA20, 0x1588, lw_branch_fail(0x134, 0x138, 11))
    g.load(0x134, "lw")
    g.branch(0x138, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_beq_f ({g.slices[('bp%d' % k, 'bl%d' % k)]}.pos_ne)")
    # The certificate's reader must be empty.
    g.block(0x13C, 0x144)
    g.load(0x144, "lw")
    rest = lean_val(g.words[0x1594])
    hz = f"hz_{g.k}"

    def fail_rest(sub):
        sub.branch(0x148, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t {hz}")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{rest} = 0", hz, fail_rest)
    g.branch(0x148, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f {hz}")
    g.store(0x14C, "sw")
    g.load(0x14E, "lw")
    for o in (0x152, 0x156, 0x15A, 0x15E):
        g.store(o, "sw")
    g.block(0x162, 0x170)
    # The version: `[0] EXPLICIT INTEGER 2`.
    k, ex, rd = g.opt(0x170, 0xA20, 0x178, 0xA0)
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with _ | (er{k} | {t})")
    g.sc.append(("eq", ex, f"some (.ok {t})", [t], f"hr{k}"))

    def fail_none(sub):
        sub.emit(f"  rw [hr{k}] at R{k}")
        sub.emit(f"  obtain ⟨y0_{k}, y4_{k}⟩ := R{k}")
        sub.frame_after(k, [(0xA20, 0x18), (0x180, 8)], {0xA24: ("0", f"y4_{k}")}, {0xA20: ("(0 : BitVec 8)", f"y0_{k}")})
        sub.load(0x178, "lbu")
        sub.branch(0x17C, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        sub.load(0x184, "lw")
        sub.branch(0x188, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        sub.block(0x1C4, 0x1C6)
        sub.jump(0x1C6)
        sub.fail(sub.fail_proof(("eq", f"hr{k}")))

    def fail_err(sub):
        sub.emit(f"  rw [hr{k}] at R{k}")
        sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
        sub.frame_after(k, [(0xA20, 0x18), (0x180, 8)], {}, {0xA20: ("(1 : BitVec 8)", f"y0_{k}")})
        sub.load(0x178, "lbu")
        sub.branch(0x17C, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.load_any(0x17E)
        sub.jump(0x182)
        sub.fail(sub.fail_proof(("eq", f"hr{k}")))
    g.fork(fail_none)
    g.fork(fail_err)
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, y12_{k}, y16_{k}, y20_{k}, d8_{k}, d12_{k}⟩ := R{k}")
    rp, rl, inp = rd
    h = f"BitVec.ofNat 32 {t}.header"
    hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
    g.frame_after(k, [(0xA20, 0x18), (0x180, 8)],
                  {0xA24: (f"({rp}) + {h}", f"y4_{k}"), 0xA28: (f"BitVec.ofNat 32 {t}.len", f"y8_{k}"),
                   0xA2C: (f"{rp}", f"y12_{k}"), 0xA30: (hl, f"y16_{k}"),
                   0x180: (f"({rp}) + {hl}", f"d8_{k}"), 0x184: (f"({rl}) - {hl}", f"d12_{k}")},
                  {0xA20: ("(0 : BitVec 8)", f"y0_{k}"), 0xA34: (f"BitVec.ofNat 8 {t}.tag", f"y20_{k}")})
    g.slices[(f"({rp}) + {h}", f"BitVec.ofNat 32 {t}.len")] = f"({inp}.contentW (opt_ok_elem hr{k}))"
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW (opt_ok_elem hr{k}))"
    g.load(0x178, "lbu")
    g.branch(0x17C, True, f"by rw [g{g.k}_10, s{g.k}.zero]; rfl")
    g.load(0x184, "lw")
    g.branch(0x188, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.ok_ne (opt_ok_elem hr{k}))")
    g.block(0x18A, 0x18C)
    g.store(0x18C, "sw")
    g.load(0x18E, "lw")
    g.block(0x192, 0x194)
    for o in (0x194, 0x196, 0x198, 0x19A):
        g.store(o, "sw")
    g.block(0x19C, 0x1A0)
    k, ex, rd = g.iis(0x1A0, 0x200)
    rp, rl, inp = rd
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with b{k} | (_ | _)")
    g.sc.append(("eq", ex, ".ok true", [], f"hr{k}"))

    def ii_regs(sub, a0, a1, how1):
        sub.emit(f"  rw [hr{k}] at R{k}")
        sub.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
        sub.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x{a0:X} := a0_{k}")
        sub.regs[10] = ("C", a0)
        if a1 is not None:
            sub.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x{a1:X} := by rw [a1_{k}]{how1}")
            sub.regs[11] = ("C", a1)
        sub.frame_after(k, [(0x208, 8)], {})

    def fail_ii_err(sub):
        ii_regs(sub, 1, None, "")
        sub.block(0x1A8, 0x1AC)
        sub.branch(0x1AC, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("eq", f"hr{k}")))

    def fail_ii_false(sub):
        ii_regs(sub, 0, 0, "; rfl")
        sub.block(0x1A8, 0x1AC)
        sub.branch(0x1AC, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.block(0x1B0, 0x1B6)
        sub.branch(0x1B6, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("eq", f"hr{k}")))
    g.fork(fail_ii_err)
    g.fork(fail_ii_false)
    g.emit(f"  obtain ⟨te{k}, hte{k}⟩ := ii_ok_elem hr{k}")
    g.sc.append(("eq", f"derElement 2 (memBytes M0 ({rp}) ({rl}).toNat)", f".ok te{k}", [f"te{k}"], f"hte{k}"))
    g.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} te{k} hte{k}")
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    g.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x0 := a0_{k}")
    g.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x1 := by rw [a1_{k}]; rfl")
    g.regs[10] = ("C", 0)
    g.regs[11] = ("C", 1)
    hl = f"BitVec.ofNat 32 (te{k}.header + te{k}.len)"
    g.frame_after(k, [(0x208, 8)], {0x208: (f"({rp}) + {hl}", f"d8_{k}"), 0x20C: (f"({rl}) - {hl}", f"d12_{k}")})
    g.block(0x1A8, 0x1AC)
    g.branch(0x1AC, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x1B0, 0x1B6)
    g.branch(0x1B6, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load(0x1BA, "lw")
    rest = lean_val(g.words[0x20C])
    hz = f"hz_{g.k}"

    def fail_vrest(sub):
        sub.branch(0x1BE, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f {hz}")
        sub.block(0x1C0, 0x1C2)
        sub.jump(0x1C2)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{rest} = 0", hz, fail_vrest)
    g.branch(0x1BE, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t {hz}")
    stmt, proof = finish(g, 0x1C8, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                         {0x78, 0x7C, 0x80, 0x84, 0x178, 0x17C, 0x180, 0x184}, set())
    binders = "{B out bp rootp dg lp ll cp cl : Word} {v : Nat → Word} {n0 : Machine}"
    info = {"name": "sv_l2", "title": "the `tbsCertificate`", "doc": "From the call to `Der::element` for the `tbsCertificate` at 0xD0 to the serial number at 0x1C8: the "
            "certificate's three parts, the empty rest, and the version, which must be `[0] EXPLICIT INTEGER 2`.", "params": params,
            "stmt": stmt, "proof": proof, "binders": binders, "start": 0xD0, "import": "C3BootProofs.Proofs.SvCongr"}
    return g, info


def stage_l3():
    """From the serial number at 0x1C8 to the call to `x509::read_time` at 0x2DC."""
    g = Gen("L3")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "lp"), 26: ("U", "ll"), 27: ("S", 0xA20), 24: ("U", "sgl"),
            25: ("U", "orl"), 22: ("U", "orp"), 8: ("U", "trl"), 9: ("U", "trp"), 23: ("U", "tcl")}
    words = {0x78: "trl", 0x7C: "sgp", 0x80: "rootp", 0x84: "dg", 0x180: "rp", 0x184: "rl"}
    params = start(g, regs, words, {("rp", "rl"): "tb_in"})
    # The serial number: a positive integer of at most 20 bytes.
    g.block(0x1C8, 0x1D2)
    k, rd = g.pos(0x1D2, 0xA20, 0x178, lw_branch_fail(0x1DA, 0x1DE, 10))
    g.load(0x1DA, "lw")
    g.branch(0x1DE, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({rd[2]}.serial_ne hr{k} hr{k}b)")
    g.load(0x1E2, "lw")
    g.block(0x1E6, 0x1E8)
    hz = f"hz_{g.k}"

    def fail_long(sub):
        sub.branch(0x1E8, True, f"by rw [g{sub.k}_10, g{sub.k}_11]; exact br_bltu_t (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega)")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"(il{k}).toNat ≤ 20", hz, fail_long)
    g.branch(0x1E8, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bltu_f (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega)")
    # The signature algorithm, which must be ecdsa-with-SHA384 with no parameters.
    g.block(0x1EC, 0x1FA)
    k, ex, rd = g.elem(0x1FA, 0xA20, 0x178, 0x30)
    t = g.elem_split(k, ex, 0xA20, 0x178, rd, lw_branch_fail(0x202, 0x206, 10))
    g.load(0x202, "lw")
    g.branch(0x206, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    g.load(0x20A, "lw")
    g.load(0x20E, "lw")
    for o in (0x212, 0x216, 0x21A, 0x21E):
        g.store(o, "sw")
    g.block(0x222, 0x232)
    k, ex, p, inp = g.alg(0x232, 0xA20, 0x1020)
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with ab{k} | ⟨⟨op{k}, ol{k}⟩, _ | ⟨prp{k}, pu{k}⟩⟩")
    g.sc.append(("eq", ex, f".ok ((op{k}, ol{k}), none)", [f"op{k}", f"ol{k}"], f"hr{k}"))
    ka = k

    def fail_alg_err(sub):
        sub.emit(f"  rw [hr{ka}] at R{ka}")
        sub.emit(f"  obtain ⟨y0_{ka}, -⟩ := R{ka}")
        sub.frame_after(ka, [(0xA20, 0x1C), (0x1028, 8)], {0xA20: ("0", f"y0_{ka}")})
        lw_branch_fail(0x23A, 0x23E, 10)(sub)
        sub.fail(sub.fail_proof(("eq", f"hr{ka}")))

    def alg_to_sne(sub, params):
        sub.emit(f"  rw [hr{ka}] at R{ka}")
        extra = "" if params == "0" else ", -, -"
        sub.emit(f"  obtain ⟨y0_{ka}, y4_{ka}, y8_{ka}{extra}⟩ := R{ka}")
        sub.frame_after(ka, [(0xA20, 0x1C), (0x1028, 8)],
                        {0xA20: (f"op{ka}", f"y0_{ka}"), 0xA24: (f"BitVec.ofNat 32 ol{ka}", f"y4_{ka}"),
                         0xA28: (params, f"y8_{ka}")})
        sub.load(0x23A, "lw")
        sub.branch(0x23E, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f ({inp}.algOid hr{ka}).pos_ne")
        sub.store(0x242, "sw")
        sub.store(0x244, "sw")
        sub.block(0x246, 0x248)
        sub.load(0x248, "lw")
        sub.load(0x24A, "lw")
        sub.block(0x24C, 0x256)
        return sub.sne(0x256, f"op{ka}", f"ol{ka}", "BitVec.ofNat 32 0x3FCC4840", "8",
                       f"(.inl ({inp}.algOid hr{ka}))", "(.inr ⟨by decide, by decide⟩)")

    oid = f"memBytes M0 op{ka} ol{ka} = memBytes M0 (BitVec.ofNat 32 0x3FCC4840) 8"

    def fail_alg_params(sub):
        sub.pinned |= {f"prp{ka}", f"pu{ka}"}
        ks = alg_to_sne(sub, f"prp{ka} + BitVec.ofNat 32 pu{ka}.header")
        sub.emit(f"  by_cases ho_{ks} : {oid}")
        sub.fork(lambda s2: alg_params_same(s2, ks))
        sub.emit(f"  have g{ks}_10 : reg n{ks} a0 = BitVec.ofNat 32 1 := by rw [a0_{ks}, ite_eq_right ho_{ks}]; rfl")
        sub.regs[10] = ("C", 1)
        sub.branch(0x25E, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("eq", f"hr{ka}")))

    def alg_params_same(s2, ks):
        s2.emit(f"  have g{ks}_10 : reg n{ks} a0 = BitVec.ofNat 32 0 := by rw [a0_{ks}, ite_eq_left ho_{ks}]; rfl")
        s2.regs[10] = ("C", 0)
        s2.branch(0x25E, False, f"by rw [g{s2.k}_10, s{s2.k}.zero]; decide")
        s2.branch(0x262, True, f"by rw [g{s2.k}_8, s{s2.k}.zero]; exact br_bne_t ({inp}.algParams hr{ka})")
        s2.fail(s2.fail_proof(("eq", f"hr{ka}")))
    g.fork(fail_alg_err)
    g.emit("  rotate_left")
    g.fork(fail_alg_params)
    ks = alg_to_sne(g, "0")
    hz = f"hz_{ks}"

    def fail_oid(sub):
        sub.emit(f"  have g{ks}_10 : reg n{ks} a0 = BitVec.ofNat 32 1 := by rw [a0_{ks}, ite_eq_right {hz}]; rfl")
        sub.regs[10] = ("C", 1)
        sub.branch(0x25E, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(oid, hz, fail_oid)
    g.emit(f"  have g{ks}_10 : reg n{ks} a0 = BitVec.ofNat 32 0 := by rw [a0_{ks}, ite_eq_left {hz}]; rfl")
    g.regs[10] = ("C", 0)
    g.branch(0x25E, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.branch(0x262, False, f"by rw [g{g.k}_8, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0x266, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27])
    binders = "{B out bp rootp dg lp ll rp rl sgl orl orp trl trp tcl sgp : Word} {v : Nat → Word} {n0 : Machine}"
    info = {"name": "sv_l3", "title": "the serial number and the signature algorithm",
            "doc": "From the serial number at 0x1C8 to 0x266: the serial number, a positive integer of at most 20 "
            "bytes, and the signature algorithm, which must be ecdsa-with-SHA384 with no parameters.",
            "params": params, "stmt": stmt, "proof": proof, "binders": binders, "start": 0x1C8,
            "import": "C3BootProofs.Proofs.SvCongr"}
    return g, info


def rt_fail_tail(off_lbu, off_br):
    """`read_time` failed: `lbu`, `bnez` to 0x17E, `lbu s4`, `j 0x966`."""
    def tail(sub):
        sub.load(off_lbu, "lbu")
        sub.branch(off_br, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.load_any(0x17E)
        sub.jump(0x182)
    return tail


def stage_l4():
    """From 0x266 to the subject at 0x318: the issuer and the validity."""
    g = Gen("L4")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "lp"), 26: ("U", "ll"), 27: ("S", 0xA20), 24: ("U", "sgl"),
            25: ("U", "orl"), 22: ("U", "orp"), 8: ("C", 0), 9: ("U", "trp"), 23: ("U", "tcl")}
    words = {0x70: "arp", 0x74: "arl", 0x78: "trl", 0x7C: "sgp", 0x80: "rootp", 0x84: "dg", 0x180: "rp", 0x184: "rl"}
    params = start(g, regs, words, {("rp", "rl"): "tb_in"})
    for o in (0x266, 0x268, 0x26A, 0x26C):
        g.store(o, "sw")
    g.block(0x26E, 0x27C)
    k, ex, rd = g.elem(0x27C, 0xA20, 0x178, 0x30)
    g.elem_split(k, ex, 0xA20, 0x178, rd, lw_branch_fail(0x284, 0x288, 10))
    g.load(0x284, "lw")
    g.branch(0x288, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    g.load(0x28C, "lw")
    g.store(0x290, "sw")
    g.load(0x292, "lw")
    g.block(0x296, 0x2A0)
    # The validity: a sequence of two times.
    k, ex, rd = g.seqr(0x2A0, 0xA20, 0x178)
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with er{k} | {t}")
    g.sc.append(("eq", ex, f".ok {t}", [t], f"hr{k}"))
    kv = k

    def fail_val(sub):
        sub.emit(f"  obtain ⟨z{kv}, -⟩ := Er{kv} er{kv} hr{kv}")
        sub.frame_after(kv, [(0xA20, 16), (0x180, 8)], {0xA20: ("0", f"z{kv}")})
        sub.load(0x2A8, "lw")
        sub.load_any(0x2AC)
        sub.branch(0x2B0, True, f"by rw [g{sub.k}_8, s{sub.k}.zero]; rfl")
        sub.fail(sub.fail_proof(("eq", f"hr{kv}")))
    g.fork(fail_val)
    g.seq_ok(k, 0xA20, 0x178, t, rd)
    g.load(0x2A8, "lw")
    g.load(0x2AC, "lbu")
    g.branch(0x2B0, False, f"by rw [g{g.k}_8, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{kv})")
    g.block(0x2B4, 0x2C2)
    g.mc(0x2C2, 0x245, 0xA25, 0xB)
    g.store(0x2CA, "sw")
    g.store(0x2CE, "sb")
    g.block(0x2D2, 0x2DC)
    k, bts, rp, rl, inp = g.rt(0x2DC, 0xA20, 0x240)
    nb, rb, hrb = g.rt_split(k, bts, 0xA20, 0x240, rp, rl, inp, rt_fail_tail(0x2E4, 0x2E8))
    g.load(0x2E4, "lbu")
    g.branch(0x2E8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x2EC, 0x2EE)
    g.load(0x2EE, "lw")
    g.store(0x2F0, "sw")
    g.load(0x2F2, "lw")
    g.store(0x2F4, "sw")
    g.block(0x2F6, 0x300)
    k, bts, rp, rl, inp = g.rt(0x300, 0xA20, 0x240, alias=hrb)
    na, ra, hra = g.rt_split(k, rb, 0xA20, 0x240, rp, rl, inp, rt_fail_tail(0x308, 0x30C))
    g.load(0x308, "lbu")
    g.branch(0x30C, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load(0x310, "lw")
    hz = f"hz_{g.k}"

    def fail_rest(sub):
        sub.branch(0x314, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t (rest_ne (by have := ({inp}.drop hkk{k}).fit; omega) {hra} {hz})")
        sub.block(0x1C0, 0x1C2)
        sub.jump(0x1C2)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{ra} = []", hz, fail_rest)
    g.branch(0x314, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f (rest_eq {hra} {hz})")
    g.block(0x318, 0x31A)
    g.load(0x31A, "lw")
    g.store(0x31C, "sw")
    g.load(0x31E, "lw")
    g.store(0x320, "sw")
    stmt, proof = finish(g, 0x322, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                         {0x4C, 0x50, 0x54, 0x58, 0x5C, 0x60, 0x64, 0x68, 0x6C, 0x70, 0x74, 0x78, 0x7C, 0x80, 0x84,
                          0x180, 0x184}, set())
    binders = ("{B out bp rootp dg lp ll rp rl sgl orl orp trp tcl sgp arp arl trl : Word} {v : Nat → Word} "
               "{n0 : Machine}")
    info = {"name": "sv_l4", "title": "the issuer and the validity",
            "doc": "From 0x266 to the subject at 0x322: the issuer, and the validity, a sequence of exactly two "
            "times.", "params": params, "stmt": stmt, "proof": proof, "binders": binders, "start": 0x266,
            "import": "C3BootProofs.Proofs.SvCongr"}
    return g, info


def spki_tail(g, op, ol, inp, ka, taken_s6):
    """From 0x3CE: compare the key's algorithm OID with id-ecPublicKey. With
    `taken_s6`, continue to `bnez s6`, which the caller takes."""
    g.block(0x3CE, 0x3DC)
    ks = g.sne(0x3DC, op, ol, "BitVec.ofNat 32 0x3FCC4914", "7", f"(.inl ({inp}.algOid hr{ka}))",
               "(.inr ⟨by decide, by decide⟩)")
    if taken_s6:
        g.block(0x3E4, 0x3E6)
    return ks


def l5_done(g, params, off):
    stmt, proof = finish(g, off, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], {0x180, 0x184}, set())
    binders = "{B out bp rootp dg lp ll rp rl x9 x22 x23 x24 x25 : Word} {v : Nat → Word} {n0 : Machine}"
    return g, {"name": "sv_l5", "title": "t", "doc": "d", "params": params, "stmt": stmt, "proof": proof,
               "binders": binders, "start": 0x322, "import": "C3BootProofs.Proofs.SvCongr"}


def stage_l5():
    """From the subject at 0x322 to 0x424: the subject and the subject public key."""
    g = Gen("L5")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 8: ("S", 0xA20),
            9: ("U", "x9"), 18: ("U", "out"), 19: ("U", "bp"), 21: ("U", "lp"), 22: ("U", "x22"),
            23: ("U", "x23"), 24: ("U", "x24"), 25: ("U", "x25"), 26: ("U", "ll"), 27: ("S", 0xA20)}
    words = {0x180: "rp", 0x184: "rl"}
    params = start(g, regs, words, {("rp", "rl"): "tb_in"})
    g.block(0x322, 0x330)
    k, ex, rd = g.elem(0x330, 0xA20, 0x178, 0x30)
    g.elem_split(k, ex, 0xA20, 0x178, rd, lw_branch_fail(0x338, 0x33A, 10))
    g.load(0x338, "lw")
    g.branch(0x33A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    # The subject public key info.
    g.block(0x33E, 0x348)
    k, ex, rd = g.seqr(0x348, 0xA20, 0x178)
    g.seq_split(k, ex, 0xA20, 0x178, rd, 0x350, 0x354, 0x358)
    if os.environ.get("SV_STOP") == "a":
        return l5_done(g, params, 0x35C)
    g.block(0x35C, 0x36E)
    g.mc(0x36E, 0x1025, 0xA25, 0xB)
    g.store(0x376, "sw")
    g.store(0x37A, "sb")
    g.block(0x37E, 0x38E)
    if os.environ.get("SV_STOP") == "b":
        return l5_done(g, params, 0x38E)
    k, ex, p, inp = g.alg(0x38E, 0xA20, 0x1020)
    nl = nat_of(lean_val(g.words[0x102C]))
    ka = k
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with ab{k} | ⟨⟨op{k}, ol{k}⟩, _ | ⟨prp{k}, pu{k}⟩⟩")
    g.sc.append(("eq", ex, f".ok ((op{k}, ol{k}), some (prp{k}, pu{k}))", [f"op{k}", f"ol{k}", f"prp{k}", f"pu{k}"],
                 f"hr{k}"))
    op, ol = f"op{ka}", f"ol{ka}"

    def fail_err(sub):
        sub.emit(f"  rw [hr{ka}] at R{ka}")
        sub.emit(f"  obtain ⟨y0_{ka}, -⟩ := R{ka}")
        sub.frame_after(ka, [(0xA20, 0x1C), (0x1028, 8)], {0xA20: ("0", f"y0_{ka}")})
        sub.load(0x396, "lw")
        sub.branch(0x39A, True, f"by rw [g{sub.k}_8, s{sub.k}.zero]; rfl")
        sub.load_any(0x962)
        sub.fail(sub.fail_proof(("eq", f"hr{ka}")))

    def fail_none(sub):
        sub.emit(f"  rw [hr{ka}] at R{ka}")
        sub.emit(f"  obtain ⟨y0_{ka}, y4_{ka}, y8_{ka}⟩ := R{ka}")
        sub.frame_after(ka, [(0xA20, 0x1C), (0x1028, 8)],
                        {0xA20: (op, f"y0_{ka}"), 0xA24: (f"BitVec.ofNat 32 {ol}", f"y4_{ka}"), 0xA28: ("0", f"y8_{ka}")})
        sub.load(0x396, "lw")
        sub.branch(0x39A, False, f"by rw [g{sub.k}_8, s{sub.k}.zero]; exact br_beq_f ({inp}.algOid hr{ka}).pos_ne")
        sub.load(0x39E, "lw")
        sub.load(0x3A2, "lw")
        sub.block(0x3A6, 0x3A8)
        sub.branch(0x3A8, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        spki_tail(sub, op, ol, inp, ka, True)
        sub.branch(0x3E6, True, f"by rw [g{sub.k}_22, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("eq", f"hr{ka}")))
    g.fork(fail_err)
    g.fork(fail_none)
    g.emit(f"  obtain ⟨ta{k}, hta{k}⟩ := alg_ok_elem hr{k}")
    g.sc.append(("eq", f"derElement 0x30 (memBytes M0 ({p}) ({nl}))", f".ok ta{k}", [f"ta{k}"], f"hta{k}"))
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, y12_{k}, y24_{k}⟩ := R{k}")
    g.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} ta{k} hta{k}")
    hl = f"BitVec.ofNat 32 (ta{k}.header + ta{k}.len)"
    rp2, rl2 = f"({p}) + {hl}", f"(BitVec.ofNat 32 ({nl})) - {hl}"
    pc = f"prp{k} + BitVec.ofNat 32 pu{k}.header"
    g.frame_after(k, [(0xA20, 0x1C), (0x1028, 8)],
                  {0xA20: (op, f"y0_{k}"), 0xA24: (f"BitVec.ofNat 32 {ol}", f"y4_{k}"), 0xA28: (pc, f"y8_{k}"),
                   0xA2C: (f"BitVec.ofNat 32 pu{k}.len", f"y12_{k}"), 0x1028: (rp2, f"d8_{k}"),
                   0x102C: (rl2, f"d12_{k}")},
                  {0xA38: (f"BitVec.ofNat 8 pu{k}.tag", f"y24_{k}")})
    g.slices[(rp2, rl2)] = f"({inp}.restN hta{k})"
    if os.environ.get("SV_STOP") == "c":
        return l5_done(g, params, 0x396)
    g.load(0x396, "lw")
    g.branch(0x39A, False, f"by rw [g{g.k}_8, s{g.k}.zero]; exact br_beq_f ({inp}.algOid hr{ka}).pos_ne")
    g.load(0x39E, "lw")
    g.load(0x3A2, "lw")
    g.block(0x3A6, 0x3A8)
    g.branch(0x3A8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.algParams hr{ka})")
    g.load(0x3AA, "lbu")
    g.block(0x3AE, 0x3B0)
    hz = f"hz_{g.k}"

    def fail_tag(sub):
        sub.branch(0x3B0, True, f"by rw [g{sub.k}_11, g{sub.k}_12]; exact br_bne_byte_t (by decide) {hz}")
        spki_tail(sub, op, ol, inp, ka, True)
        sub.branch(0x3E6, True, f"by rw [g{sub.k}_22, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"BitVec.ofNat 8 pu{ka}.tag = BitVec.ofNat 8 6", hz, fail_tag)
    g.branch(0x3B0, False, f"by rw [g{g.k}_11, g{g.k}_12]; exact br_bne_byte_f (by decide) {hz}")
    g.load(0x3B4, "lw")
    g.block(0x3B8, 0x3C2)
    ke = g.seqeq(0x3C2, pc, f"pu{ka}.len", "BitVec.ofNat 32 0x3FCC4848", "8", f"(.inl ({inp}.algParamsIn hr{ka}))",
                 "(.inr ⟨by decide, by decide⟩)")
    curve = f"memBytes M0 ({pc}) pu{ka}.len = memBytes M0 (BitVec.ofNat 32 0x3FCC4848) 8"
    hz = f"hz_{ke}"

    def fail_curve(sub):
        sub.set_a0(ke, 0, f"ite_eq_right {hz}")
        sub.block(0x3CA, 0x3CE)
        spki_tail(sub, op, ol, inp, ka, True)
        sub.branch(0x3E6, True, f"by rw [g{sub.k}_22, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(curve, hz, fail_curve)
    g.set_a0(ke, 1, f"ite_eq_left {hz}")
    g.block(0x3CA, 0x3CE)
    ks = spki_tail(g, op, ol, inp, ka, False)
    oid = f"memBytes M0 {op} {ol} = memBytes M0 (BitVec.ofNat 32 0x3FCC4914) 7"
    hz = f"hz_{ks}"

    def fail_oid(sub):
        sub.set_a0(ks, 1, f"ite_eq_right {hz}")
        sub.block(0x3E4, 0x3E6)
        sub.branch(0x3E6, False, f"by rw [g{sub.k}_22, s{sub.k}.zero]; decide")
        sub.branch(0x3EA, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(oid, hz, fail_oid)
    g.set_a0(ks, 0, f"ite_eq_left {hz}")
    g.block(0x3E4, 0x3E6)
    g.branch(0x3E6, False, f"by rw [g{g.k}_22, s{g.k}.zero]; decide")
    g.branch(0x3EA, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    if os.environ.get("SV_STOP") == "d":
        return l5_done(g, params, 0x3EE)
    # The key: a BIT STRING of 65 bytes that ends the subject public key info.
    g.block(0x3EE, 0x3FE)
    k = g.bits(0x3FE, 0xA20, 0x1020, lw_branch_fail(0x406, 0x40A, 10))
    g.load(0x406, "lw")
    g.branch(0x40A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[('bp%d' % k, 'bl%d' % k)]}.pos_ne)")
    if os.environ.get("SV_STOP") == "e":
        return l5_done(g, params, 0x40E)
    g.block(0x40E, 0x410)
    if os.environ.get("SV_STOP") == "e1":
        return l5_done(g, params, 0x410)
    g.load(0x410, "lw")
    if os.environ.get("SV_STOP") == "e2":
        return l5_done(g, params, 0x414)
    g.block(0x414, 0x418)
    if os.environ.get("SV_STOP") == "f":
        return l5_done(g, params, 0x418)
    hz = f"hz_{g.k}"

    def fail_len(sub):
        sub.branch(0x418, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t (sub_lit_ne (c := 0x41) (by decide) {hz})")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"bl{k} = BitVec.ofNat 32 0x41", hz, fail_len)
    g.branch(0x418, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f (sub_lit_eq (c := 0x41) (by decide) {hz})")
    g.load(0x41C, "lw")
    rest = lean_val(g.words[0x102C])
    hz = f"hz_{g.k}"

    def fail_rest(sub):
        sub.branch(0x420, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t {hz}")
        sub.block(0x1C0, 0x1C2)
        sub.jump(0x1C2)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{rest} = 0", hz, fail_rest)
    g.branch(0x420, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f {hz}")
    stmt, proof = finish(g, 0x424, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                         {0x180, 0x184}, set())
    binders = "{B out bp rootp dg lp ll rp rl x9 x22 x23 x24 x25 : Word} {v : Nat → Word} {n0 : Machine}"
    info = {"name": "sv_l5", "title": "the subject and its public key",
            "doc": "From the subject at 0x322 to 0x424: the subject, and the subject public key info, whose "
            "algorithm must be id-ecPublicKey with the P-256 curve and whose key must be a 65-byte BIT STRING.",
            "params": params, "stmt": stmt, "proof": proof, "binders": binders, "start": 0x322,
            "import": "C3BootProofs.Proofs.SvCongr"}
    return g, info


def stage_l6():
    """From 0x424 to the extensions loop at 0x4EA."""
    g = Gen("L6")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 8: ("U", "x8"),
            9: ("U", "x9"), 18: ("U", "out"), 19: ("U", "bp"), 21: ("U", "kp"), 22: ("U", "x22"),
            23: ("U", "x23"), 24: ("U", "x24"), 25: ("U", "x25"), 26: ("U", "ll"), 27: ("S", 0xA20)}
    words = {0x180: "rp", 0x184: "rl"}
    params = start(g, regs, words, {("rp", "rl"): "tb_in"})
    params += ["(kb_in : SvIn B kp 0x41)", "(D0 : P2Data M0)"]
    # The key: tag 4, then a point on the curve.
    g.load_in(0x424, "kb_in")
    g.block(0x428, 0x42C)
    hz = f"hz_{g.k}"

    def fail_tag(sub):
        sub.branch(0x42C, True, f"by rw [g{sub.k}_10, g{sub.k}_11]; exact br_bne_byte_t (by decide) {hz}")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("M0 kp = BitVec.ofNat 8 4", hz, fail_tag)
    g.branch(0x42C, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bne_byte_f (by decide) {hz}")
    g.block(0x430, 0x43A)
    k = g.gs(0x43A, 0xA20, "kb_in")
    hz = f"hz_{k}"

    def fail_gs(sub):
        sub.emit(f"  have y0_{k} := Er{k} {hz}")
        sub.frame_after(k, [(0xA20, 0x48)], {0xA20: ("1", f"y0_{k}")})
        sub.load(0x442, "lw")
        sub.branch(0x446, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("GsOk M0 kp", hz, fail_gs)
    g.emit(f"  have y0_{k} := Ok{k} {hz}")
    g.frame_after(k, [(0xA20, 0x48)], {0xA20: ("0", f"y0_{k}")})
    g.load(0x442, "lw")
    g.branch(0x446, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    # The extensions: `[3] EXPLICIT`, the last part of the tbsCertificate.
    g.block(0x44A, 0x458)
    k, ex, rd = g.opt(0x458, 0xA20, 0x178, 0xA3)
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with _ | (er{k} | {t})")
    g.sc.append(("eq", ex, f"some (.ok {t})", [t], f"hr{k}"))

    def fail_none(sub):
        sub.emit(f"  rw [hr{k}] at R{k}")
        sub.emit(f"  obtain ⟨y0_{k}, y4_{k}⟩ := R{k}")
        sub.frame_after(k, [(0xA20, 0x18), (0x180, 8)], {0xA24: ("0", f"y4_{k}")}, {0xA20: ("(0 : BitVec 8)", f"y0_{k}")})
        sub.load(0x460, "lbu")
        sub.branch(0x464, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.load(0x468, "lw")
        sub.block(0x46C, 0x46E)
        sub.branch(0x46E, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        sub.fail(sub.fail_proof(("eq", f"hr{k}")))

    def fail_err(sub):
        sub.emit(f"  rw [hr{k}] at R{k}")
        sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
        sub.frame_after(k, [(0xA20, 0x18), (0x180, 8)], {}, {0xA20: ("(1 : BitVec 8)", f"y0_{k}")})
        sub.load(0x460, "lbu")
        sub.branch(0x464, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.load_any(0x17E)
        sub.jump(0x182)
        sub.fail(sub.fail_proof(("eq", f"hr{k}")))
    g.fork(fail_none)
    g.fork(fail_err)
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, y12_{k}, y16_{k}, y20_{k}, d8_{k}, d12_{k}⟩ := R{k}")
    rp, rl, inp = rd
    h = f"BitVec.ofNat 32 {t}.header"
    hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
    g.frame_after(k, [(0xA20, 0x18), (0x180, 8)],
                  {0xA24: (f"({rp}) + {h}", f"y4_{k}"), 0xA28: (f"BitVec.ofNat 32 {t}.len", f"y8_{k}"),
                   0xA2C: (f"{rp}", f"y12_{k}"), 0xA30: (hl, f"y16_{k}"),
                   0x180: (f"({rp}) + {hl}", f"d8_{k}"), 0x184: (f"({rl}) - {hl}", f"d12_{k}")},
                  {0xA20: ("(0 : BitVec 8)", f"y0_{k}"), 0xA34: (f"BitVec.ofNat 8 {t}.tag", f"y20_{k}")})
    g.slices[(f"({rp}) + {h}", f"BitVec.ofNat 32 {t}.len")] = f"({inp}.contentW (opt_ok_elem hr{k}))"
    g.load(0x460, "lbu")
    g.branch(0x464, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load(0x468, "lw")
    g.block(0x46C, 0x46E)
    g.branch(0x46E, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.ok_ne (opt_ok_elem hr{k}))")
    g.load(0x472, "lw")
    rest = lean_val(g.words[0x184])
    hz = f"hz_{g.k}"

    def fail_trest(sub):
        sub.branch(0x476, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; exact br_bne_t {hz}")
        sub.block(0x1C0, 0x1C2)
        sub.jump(0x1C2)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{rest} = 0", hz, fail_trest)
    g.branch(0x476, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_bne_f {hz}")
    g.load(0x47A, "lw")
    g.block(0x47E, 0x486)
    for o in (0x486, 0x488, 0x48A):
        g.store(o, "sw")
    g.block(0x48C, 0x496)
    g.store(0x496, "sw")
    g.block(0x498, 0x4AC)
    k, ex, rd = g.elem(0x4AC, 0xA20, 0x1320, 0x30)
    g.elem_split(k, ex, 0xA20, 0x1320, rd, lw_branch_fail(0x4B4, 0x4B8, 10))
    g.load(0x4B4, "lw")
    g.branch(0x4B8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    g.load(0x4BC, "lw")
    rest = lean_val(g.words[0x132C])
    hz = f"hz_{g.k}"

    def fail_xrest(sub):
        sub.branch(0x4BE, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; exact br_bne_t {hz}")
        sub.block(0x1C0, 0x1C2)
        sub.jump(0x1C2)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{rest} = 0", hz, fail_xrest)
    g.branch(0x4BE, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_bne_f {hz}")
    g.load(0x4C2, "lw")
    for o in (0x4C6, 0x4C8, 0x4CA, 0x4CC, 0x4CE):
        g.store(o, "sw")
    # Clear the five identity-policy slots.
    g.block(0x4D0, 0x4DA)
    g.branch(0x4DA, False, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
    for i in range(5):
        g.store(0x4DC, "sw")
        g.block(0x4E0, 0x4E4)
        g.branch(0x4E4, i < 4, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
    g.store(0x4E6, "sw")
    g.store(0x4E8, "sw")
    stmt, proof = finish(g, 0x4EA, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                         {0x30, 0x34, 0x40, 0x88, 0x8C, 0x90, 0x94, 0xA20, 0xA24, 0xA28, 0xA2C, 0xA30, 0xA34, 0xA38,
                          0xA3C, 0xA40, 0xA44}, set())
    binders = "{B out bp rootp dg lp ll rp rl kp x8 x9 x22 x23 x24 x25 : Word} {v : Nat → Word} {n0 : Machine}"
    info = {"name": "sv_l6", "title": "the leaf's key and the extensions' start",
            "doc": "From 0x424 to the extensions loop at 0x4EA: the key is tag 4 and a point on P-256, the "
            "tbsCertificate ends with `[3] EXPLICIT` extensions that hold one `SEQUENCE`, and the five "
            "identity-policy slots and the two flags start at zero.",
            "params": params, "stmt": stmt, "proof": proof, "binders": binders, "start": 0x424,
            "import": "C3BootProofs.Proofs.SvP256"}
    return g, info


def loop_start(g, extra_regs=None):
    """The extensions loop's facts at its head, 0x4EA."""
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 27: ("S", 0xA20), 9: ("U", "x9"), 21: ("U", "x21"), 25: ("U", "x25"), 26: ("U", "x26")}
    regs.update(extra_regs or {})
    words = {0x30: "f30", 0x34: "f34", 0x40: "rem", 0x88: "p0", 0x8C: "L", 0x90: "cur", 0x94: "rem"}
    for i in range(10):
        words[0xA20 + 4 * i] = f"sl{i}"
    for e in range(0x4C, 0x88, 4):
        words[e] = f"w{e:x}"
    return start(g, regs, words, {("cur", "rem"): "xl_in"})


LOOP_KEEP = {0x30, 0x34, 0x88, 0x8C} | {0xA20 + 4 * i for i in range(10)} | set(range(0x4C, 0x88, 4))
LOOP_BINDERS = ("{B out bp x9 x21 x25 x26 f30 f34 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 "
                + " ".join(f"w{e:x}" for e in range(0x4C, 0x88, 4)) + " : Word} {v : Nat → Word} {n0 : Machine}")


def stage_x1():
    """One pass of the extensions loop, from its head at 0x4EA to the
    criticality test at 0x560: the next extension's `SEQUENCE` and its OID."""
    g = Gen("X1")
    params = loop_start(g)
    params += ["(ea_in : SvIn B p0 (L.toNat - rem.toNat))", "(hrem : rem ≠ 0)"]
    g.load(0x4EA, "lw")
    g.branch(0x4EC, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hrem")
    g.load(0x4F0, "lw")
    g.load(0x4F2, "lw")
    hz = f"hz_{g.k}"

    def fail_len(sub):
        sub.branch(0x4F4, True, f"by rw [g{sub.k}_22, g{sub.k}_10]; exact br_bltu_t (by omega)")
        err44(sub, 0xB2E)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("rem.toNat ≤ L.toNat", hz, fail_len)
    g.branch(0x4F4, False, f"by rw [g{g.k}_22, g{g.k}_10]; exact br_bltu_f (by omega)")
    g.load(0x4F8, "lw")
    g.block(0x4FA, 0x504)
    k, ex, rd = g.seqr(0x504, 0x1020, 0x88)
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with er{k} | {t}")
    g.sc.append(("eq", ex, f".ok {t}", [t], f"hr{k}"))
    ks = k

    def fail_seq(sub):
        sub.emit(f"  obtain ⟨z{ks}, -⟩ := Er{ks} er{ks} hr{ks}")
        sub.frame_after(ks, [(0x1020, 16), (0x90, 8)], {0x1020: ("0", f"z{ks}")})
        sub.load(0x50C, "lw")
        sub.load_any(0x510)
        sub.store(0x514, "sw")
        sub.branch(0x516, True, f"by rw [g{sub.k}_8, s{sub.k}.zero]; rfl")
        err44(sub, 0xB46)
        sub.fail(sub.fail_proof(("eq", f"hr{ks}")))
    g.fork(fail_seq)
    g.seq_ok(k, 0x1020, 0x88, t, rd)
    g.load(0x50C, "lw")
    g.load(0x510, "lbu")
    g.store(0x514, "sw")
    g.branch(0x516, False, f"by rw [g{g.k}_8, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{ks})")
    g.block(0x51A, 0x528)
    g.mc(0x528, 0x325, 0x1025, 0xB)
    g.store(0x530, "sw")
    g.load(0x534, "lw")
    g.store(0x536, "sb")
    g.block(0x53A, 0x544)

    def oid_tail(sub):
        sub.load(0x54C, "lw")
        sub.branch(0x550, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        err44(sub, 0x9BA)
    k, op, ol = g.oid(0x544, 0x1020, 0x320, oid_tail)
    g.load(0x54C, "lw")
    g.branch(0x550, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(op, ol)]}.pos_ne)")
    g.block(0x554, 0x556)
    g.load(0x556, "lw")
    g.load(0x55A, "lw")
    g.store(0x55E, "sw")
    stmt, proof = finish(g, 0x560, [2, 3, 4, 8, 9, 10, 11, 18, 19, 21, 22, 24, 25, 26, 27],
                         LOOP_KEEP | {0x40, 0x48, 0x90, 0x94, 0x320, 0x324, 0x328, 0x32C}, set())
    info = {"name": "sv_x1", "title": "an extension's OID",
            "doc": "One pass of the extensions loop, from its head at 0x4EA to the criticality test at 0x560: "
            "the next extension is a `SEQUENCE` that starts with an OID.",
            "params": params, "stmt": stmt, "proof": proof, "binders": LOOP_BINDERS, "start": 0x4EA,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


def x2_start(g):
    regs = {8: ("U", "op"), 10: ("U", "rem2"), 11: ("U", "ol"), 22: ("U", "L"), 24: ("U", "p0")}
    params = loop_start(g, regs)
    for e in (0x90, 0x94):
        g.words.pop(e)
    params = [x for x in params if not any(x.startswith(f"(w0_{e:x} ") for e in (0x90, 0x94))
               and not x.startswith("(xl_in")]
    g.slices = {}
    for e, v in {0x48: "ol", 0x90: "cur", 0x94: "rest", 0x328: "rp2", 0x32C: "rem2"}.items():
        g.words[e] = ("U", v)
        params.append(f"(w0_{e:x} : memLoad32 n0.mem ({fa(e)}) = {v})")
    g.slices[("rp2", "rem2")] = "in2"
    g.slices[("op", "ol")] = "oid_in"
    params += ["(in2 : SvIn B rp2 rem2.toNat)", "(oid_in : SvIn B op ol.toNat)",
               "(ea_in : SvIn B p0 (L.toNat - rem.toNat))", "(hle : rem.toNat ≤ L.toNat)"]
    return params


def x2_tail(g):
    """From 0x58E: the extension's value, an OCTET STRING that ends it, and its
    OID not among the earlier extensions'. Ends before `beqz s7` at 0x5E0."""
    g.block(0x58E, 0x598)

    def oct_tail(sub):
        sub.load(0x5A0, "lw")
        sub.store(0x5A4, "sw")
        sub.branch(0x5A6, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        err44(sub, 0x9BA)
    k, vp, vl = g.oct(0x598, 0x1020, 0x320, oct_tail)
    g.load(0x5A0, "lw")
    g.store(0x5A4, "sw")
    g.branch(0x5A6, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(vp, vl)]}.pos_ne)")
    g.load(0x5AA, "lw")
    rest = lean_val(g.words[0x32C])
    hz = f"hz_{g.k}"

    def fail_inner(sub):
        sub.branch(0x5AE, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t {hz}")
        err44(sub, 0xB36)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{rest} = 0", hz, fail_inner)
    g.branch(0x5AE, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f {hz}")
    g.load(0x5B2, "lw")
    g.store(0x5B6, "sw")
    g.load(0x5B8, "lw")
    g.block(0x5BA, 0x5C2)
    k = g.k
    g.emit(f"  rw [sub_ofNat_toNat hle] at g{k}_11")
    g.regs[11] = ("U", "BitVec.ofNat 32 (L.toNat - rem.toNat)")
    g.load(0x5C2, "lw")
    kl = g.lo(0x5C4, "p0", "L.toNat - rem.toNat", "op", "ol.toNat", "ea_in", "oid_in")
    ex = "listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat)"
    g.emit(f"  obtain ⟨r{kl}, hr{kl}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{kl} with lb{kl} | (_ | _)")
    g.sc.append(("eq", ex, ".ok false", [], f"hr{kl}"))

    def lo_regs(sub, a0, a1, a1v):
        sub.emit(f"  rw [hr{kl}] at R{kl}")
        sub.emit(f"  obtain ⟨a0_{kl}, a1_{kl}⟩ := R{kl}")
        sub.emit(f"  have g{sub.k}_10 : reg n{sub.k} a0 = BitVec.ofNat 32 0x{a0:X} := a0_{kl}")
        sub.regs[10] = ("C", a0)
        if a1 is not None:
            sub.emit(f"  have g{sub.k}_11 : reg n{sub.k} a1 = BitVec.ofNat 32 0x{a1:X} := by rw [a1_{kl}]; rfl")
            sub.regs[11] = ("C", a1)
        elif a1v is not None:
            sub.emit(f"  have g{sub.k}_11 : reg n{sub.k} a1 = {a1v} := a1_{kl}")
            sub.regs[11] = ("U", a1v)

    def fail_lo_err(sub):
        lo_regs(sub, 1, None, f"(lb{kl}).zeroExtend 32")
        sub.block(0x5CC, 0x5CE)
        sub.store(0x5CE, "sw")
        sub.branch(0x5D0, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        err44(sub, 0xB46)
        sub.fail(sub.fail_proof(("eq", f"hr{kl}")))

    def fail_lo_dup(sub):
        lo_regs(sub, 0, 1, None)
        sub.block(0x5CC, 0x5CE)
        sub.store(0x5CE, "sw")
        sub.branch(0x5D0, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.load(0x5D4, "lw")
        sub.block(0x5D6, 0x5DA)
        sub.store(0x5DA, "sw")
        sub.branch(0x5DC, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        err44(sub, 0xB46)
        sub.fail(sub.fail_proof(("eq", f"hr{kl}")))
    g.fork(fail_lo_err)
    g.emit("  rotate_left")
    g.fork(fail_lo_dup)
    lo_regs(g, 0, 0, None)
    g.block(0x5CC, 0x5CE)
    g.store(0x5CE, "sw")
    g.branch(0x5D0, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load(0x5D4, "lw")
    g.block(0x5D6, 0x5DA)
    g.store(0x5DA, "sw")
    g.branch(0x5DC, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")


X2_KEEP_REGS = [2, 3, 4, 8, 9, 18, 19, 21, 25, 26, 27]
X2_KEEP_WORDS = LOOP_KEEP | {0x38, 0x3C, 0x40, 0x48, 0x90, 0x94}
X2_BINDERS = LOOP_BINDERS.replace(" : Word}", " op rem2 ol rest rp2 : Word}")


def stage_x2n():
    """From the criticality test at 0x560 to the OID tests at 0x60E, for an
    extension whose next byte isn't 1: not critical."""
    g = Gen("X2n")
    params = x2_start(g)
    params += ["(hr2 : rem2 ≠ 0)", "(hb1 : M0 rp2 ≠ BitVec.ofNat 8 1)"]
    g.branch(0x560, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hr2")
    g.load(0x562, "lw")
    g.load_in(0x566, "in2", "(toNat_pos_of_ne hr2)")
    g.block(0x56A, 0x56C)
    g.branch(0x56C, True, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bne_byte_t (by decide) hb1")
    g.block(0x58C, 0x58E)
    x2_tail(g)
    g.branch(0x5E0, True, f"by rw [g{g.k}_23, s{g.k}.zero]; rfl")
    stmt, proof = finish(g, 0x60E, X2_KEEP_REGS, X2_KEEP_WORDS, set())
    info = {"name": "sv_x2n", "title": "a noncritical extension's value",
            "doc": "From the criticality test at 0x560 to the OID tests at 0x60E, for an extension whose next "
            "byte isn't 1: its value is an OCTET STRING that ends it, and its OID isn't an earlier extension's.",
            "params": params, "stmt": stmt, "proof": proof, "binders": X2_BINDERS, "start": 0x560,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


def stage_x2z():
    """From 0x560, for an extension that ends after its OID: no value."""
    g = Gen("X2z")
    params = x2_start(g)
    params += ["(hr2 : rem2 = 0)"]
    g.branch(0x560, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hr2")
    g.block(0x58C, 0x58E)
    g.block(0x58E, 0x598)

    def oct_tail(sub):
        sub.load(0x5A0, "lw")
        sub.store(0x5A4, "sw")
        sub.branch(0x5A6, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        err44(sub, 0x9BA)
    k, vp, vl = g.oct(0x598, 0x1020, 0x320, oct_tail)
    stmt, _ = finish(g, 0x5A0, X2_KEEP_REGS, set(), set())
    lines = g.out
    i = max(j for j, l in enumerate(lines) if l.startswith("  obtain ⟨te"))
    g.out = lines[:i] + [f"  exact absurd hr{k} (content_empty (w0_32c.symm.trans (by rw [hr2]) |> fun h => by simpa using hr2))"]
    g.out[-1] = f"  exact absurd hr{k} (content_empty hr2)"
    info = {"name": "sv_x2z", "title": "an extension with no value",
            "doc": "From 0x560, for an extension that ends after its OID: `Der::octet_string` finds no value, "
            "and `sigstore::verify` fails.",
            "params": params, "stmt": stmt, "proof": "", "binders": X2_BINDERS, "start": 0x560,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


CRIT = [0x3FCC4889 + 3 * i for i in range(4)]


def crit_allowed():
    x = "memBytes M0 op ol.toNat"
    return " ∨ ".join(f"memBytes M0 (BitVec.ofNat 32 0x{a:X}) 3 = {x}" for a in CRIT)


def crit_proof(i, h):
    t = h if i == 3 else f".inl {h}"
    for _ in range(i):
        t = f".inr ({t})"
    return f"({t})"


def stage_x2c():
    """From the criticality test at 0x560 to the OID tests at 0x60E, for a
    critical extension."""
    g = Gen("X2c")
    params = x2_start(g)
    params += ["(hr2 : rem2 ≠ 0)", "(hb1 : M0 rp2 = BitVec.ofNat 8 1)", "(SD0 : SvData M0)"]
    g.branch(0x560, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hr2")
    g.load(0x562, "lw")
    g.load_in(0x566, "in2", "(toNat_pos_of_ne hr2)")
    g.block(0x56A, 0x56C)
    g.branch(0x56C, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bne_byte_f (by decide) hb1")
    g.block(0x570, 0x572)
    k, ex, rd = g.boolt(0x572, 0x320)
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with eb{k} | ⟨⟩")
    g.sc.append(("eq", ex, ".ok ()", [], f"hr{k}"))
    kb = k

    def fail_bool(sub):
        sub.emit(f"  have g{kb}_10 : reg n{kb} a0 = (derErrByte eb{kb}).zeroExtend 32 := by rw [a0_{kb}, hr{kb}]; rfl")
        sub.regs[10] = ("U", f"(derErrByte eb{kb}).zeroExtend 32")
        sub.frame_after(kb, [(0x328, 8)], {})
        sub.store(0x57A, "sw")
        sub.block(0x57C, 0x580)
        sub.block(0x580, 0x584)
        sub.branch(0x584, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t (derErr_ff_ne eb{kb})")
        err44(sub, 0xB46)
        sub.fail(sub.fail_proof(("eq", f"hr{kb}")))
    g.fork(fail_bool)
    g.emit(f"  have g{kb}_10 : reg n{kb} a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [a0_{kb}, hr{kb}]; rfl")
    g.regs[10] = ("C", 0xFFFFFFFF)
    tb = f"tb{kb}"
    g.emit(f"  obtain ⟨{tb}, htb{kb}⟩ := bool_ok_elem hr{kb}")
    rp, rl, inp = rd
    L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
    g.sc.append(("eq", f"derElement 1 {L}", f".ok {tb}", [tb], f"htb{kb}"))
    g.emit(f"  obtain ⟨d8_{kb}, d12_{kb}⟩ := A{kb} {tb} htb{kb}")
    hl = f"BitVec.ofNat 32 ({tb}.header + {tb}.len)"
    g.frame_after(kb, [(0x328, 8)], {0x328: (f"({rp}) + {hl}", f"d8_{kb}"), 0x32C: (f"({rl}) - {hl}", f"d12_{kb}")})
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW htb{kb})"
    g.store(0x57A, "sw")
    g.block(0x57C, 0x584)
    g.branch(0x584, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x588, 0x58A)
    g.jump(0x58A)
    x2_tail(g)
    g.branch(0x5E0, False, f"by rw [g{g.k}_23, s{g.k}.zero]; decide")
    g.block(0x5E4, 0x5F0)
    P = crit_allowed()
    for i in range(4):
        g.branch(0x5F0, False, f"by rw [g{g.k}_22, s{g.k}.zero]; decide")
        g.load_data(0x5F4, CRIT[i], 0x80 + 8 * i)
        g.load_data(0x5F8, 3, 0x84 + 8 * i)
        g.block(0x5FC, 0x5FE)
        g.load(0x5FE, "lw")
        ke = g.seqeq(0x600, f"BitVec.ofNat 32 0x{CRIT[i]:X}", "3", "op", "ol.toNat", "(.inr ⟨by decide, by decide⟩)",
                     "(.inl oid_in)", f"(by rw [g{g.k}_13, ofNat_toNat_self])")
        eq = f"memBytes M0 (BitVec.ofNat 32 0x{CRIT[i]:X}) 3 = memBytes M0 op ol.toNat"
        hm = f"hm{i}"
        g.emit(f"  by_cases {hm} : {eq}")
        if i < 3:
            def matched(sub, i=i, ke=ke, hm=hm):
                sub.set_a0(ke, 1, f"ite_eq_left {hm}")
                sub.block(0x608, 0x60C)
                sub.branch(0x60C, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
                sub.sc.append(("prop", P, crit_proof(i, hm)))
                sub.exit_here()
            g.fork(matched)
            g.set_a0(ke, 0, f"ite_eq_right {hm}")
            g.block(0x608, 0x60C)
            g.branch(0x60C, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        else:
            def missed(sub, ke=ke, hm=hm):
                sub.set_a0(ke, 0, f"ite_eq_right {hm}")
                sub.block(0x608, 0x60C)
                sub.branch(0x60C, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
                sub.branch(0x5F0, True, f"by rw [g{sub.k}_22, s{sub.k}.zero]; decide")
                err44(sub, 0xB46)
                sub.emit(f"  have hna : ¬ ({P}) := fun h => h.elim hm0 (fun h => h.elim hm1 (fun h => h.elim hm2 hm3))")
                sub.sc.append(("prop", P, "_"))
                sub.fail(sub.fail_proof(("prop", "hna")))
            g.emit("  rotate_left")
            g.fork(missed)
            g.set_a0(ke, 1, f"ite_eq_left {hm}")
            g.block(0x608, 0x60C)
            g.branch(0x60C, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            g.sc.append(("prop", P, crit_proof(3, hm)))
    stmt, proof = finish(g, 0x60E, X2_KEEP_REGS, X2_KEEP_WORDS, set())
    info = {"name": "sv_x2c", "title": "a critical extension's value",
            "doc": "From the criticality test at 0x560 to the OID tests at 0x60E, for a critical extension: "
            "`BOOLEAN TRUE`, a value that ends it, an OID that isn't an earlier extension's, and one of the four "
            "OIDs that may be critical.",
            "params": params, "stmt": stmt, "proof": proof, "binders": X2_BINDERS, "start": 0x560,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


KU_C, EKU_C, BC_C = 0x3FCC4889, 0x3FCC4892, 0x3FCC488F
POL = [0x3FCC48B8 + 10 * i for i in range(5)]


def oid_is(c):
    return f"memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x{c:X}) 3"


def pol_is(i):
    return f"memBytes M0 (BitVec.ofNat 32 0x{POL[i]:X}) 10 = memBytes M0 op ol.toNat"


def d_start(g):
    """The facts at the OID tests, 0x60E."""
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 27: ("S", 0xA20), 9: ("U", "x9"), 21: ("U", "x21"), 25: ("U", "x25"),
            26: ("U", "x26"), 8: ("U", "op")}
    words = {0x30: "f30", 0x34: "f34", 0x38: "vl", 0x3C: "vp", 0x40: "rem", 0x48: "ol", 0x88: "p0", 0x8C: "L",
             0x90: "cur", 0x94: "rest"}
    for i in range(10):
        words[0xA20 + 4 * i] = f"sl{i}"
    for e in range(0x4C, 0x88, 4):
        words[e] = f"w{e:x}"
    params = start(g, regs, words, {("vp", "vl"): "val_in", ("op", "ol"): "oid_in"})
    params += ["(SD0 : SvData M0)"]
    return params


def d_test(g, at, c, want, hname):
    """The test at `at` of the OID against the 3-byte one at `c`: `want` says
    whether the extension's OID is that one."""
    g.block(at, at + 4)
    g.load(at + 4, "lw")
    g.block(at + 6, at + 0xE)
    ke = g.seqeq(at + 0xE, "op", "ol.toNat", f"BitVec.ofNat 32 0x{c:X}", "3", "(.inl oid_in)",
                 "(.inr ⟨by decide, by decide⟩)", ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
    g.set_a0(ke, 1 if want else 0, f"ite_eq_left {hname}" if want else f"ite_eq_right {hname}")
    g.branch(at + 0x16, not want, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")


def d_next(g):
    """From 0x95C: the reader's new length becomes `rem`, and back to the head."""
    g.load(0x95C, "lw")
    g.store(0x95E, "sw")
    g.jump(0x960)


def d_policy_loop(g, upto):
    """The policy OID table, missed `upto` times (and matched next, below 5)."""
    g.block(0x89C, 0x8A6)
    for i in range(upto + (1 if upto < 5 else 0)):
        g.block(0x8A6, 0x8A8)
        g.branch(0x8A8, False, f"by rw [g{g.k}_22, g{g.k}_10]; decide")
        g.load_data(0x8AC, POL[i], 0xD4 + 8 * i)
        g.block(0x8B0, 0x8B4)
        g.load(0x8B4, "lw")
        ke = g.seqeq(0x8B6, f"BitVec.ofNat 32 0x{POL[i]:X}", "10", "op", "ol.toNat", "(.inr ⟨by decide, by decide⟩)",
                     "(.inl oid_in)", f"(by rw [g{g.k}_13, ofNat_toNat_self])")
        hit = i == upto
        g.set_a0(ke, 1 if hit else 0, f"ite_eq_left hp{i}" if hit else f"ite_eq_right hp{i}")
        g.block(0x8BE, 0x8C2)
        g.branch(0x8C2, not hit, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    if upto == 5:
        g.block(0x8A6, 0x8A8)
        g.branch(0x8A8, True, f"by rw [g{g.k}_22, g{g.k}_10]; decide")


D_KEEP_REGS = [2, 3, 4, 9, 18, 19, 21, 25, 26, 27]
D_KEEP_WORDS = LOOP_KEEP | {0x40, 0x90, 0x94}
D_BINDERS = LOOP_BINDERS.replace(" : Word}", " op ol vp vl rest : Word}")


def stage_dpol(i):
    """From the OID tests at 0x60E back to the loop head, for an extension
    whose OID is policy OID `i`, or none of the OIDs `sigstore::verify` reads
    when `i` is 5."""
    def gen():
        g = Gen(f"Dp{i}")
        params = d_start(g)
        params += [f"(hku : ¬ {oid_is(KU_C)})", f"(heku : ¬ {oid_is(EKU_C)})", f"(hbc : ¬ {oid_is(BC_C)})"]
        params += [f"(hp{j} : ¬ {pol_is(j)})" for j in range(i)]
        if i < 5:
            params.append(f"(hp{i} : {pol_is(i)})")
        d_test(g, 0x60E, KU_C, False, "hku")
        d_test(g, 0x6BC, EKU_C, False, "heku")
        d_test(g, 0x78E, BC_C, False, "hbc")
        d_policy_loop(g, i)
        if i < 5:
            g.block(0x8C4, 0x8CC)
            g.load(0x8CC, "lw")
            g.block(0x8CE, 0x8D2)
            g.store(0x8D2, "sw")
            g.load(0x8D4, "lw")
            g.store(0x8D6, "sw")
            g.store(0x8D8, "sw")
            g.block(0x8DA, 0x8E4)
            g.store(0x8E4, "sw")
            g.block(0x8E6, 0x8F6)
            k = g.tlv(0x8F6, 0x1020, 0x1480, lambda sub: (sub.load(0x8FE, "lw"),
                      sub.branch(0x902, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl"), err44(sub, 0x9BA)))
            t = g.last_tlv
            g.load(0x8FE, "lw")
            g.branch(0x902, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f (val_in.tlv_ne hr{k})")
            g.load(0x904, "lbu")
            g.block(0x908, 0x90A)
            hz = f"hz_{g.k}"

            def fail_tag(sub):
                sub.branch(0x90A, True, f"by rw [g{sub.k}_11, g{sub.k}_12]; exact br_bne_byte_t (by decide) {hz}")
                sub.block(0xB4E, 0xB50)
                sub.jump(0xB50)
                err44(sub, 0xB38)
                sub.fail(sub.fail_proof(("prop", hz)))
            g.prop_check(f"BitVec.ofNat 8 {t}.tag = BitVec.ofNat 8 0xC", hz, fail_tag)
            g.branch(0x90A, False, f"by rw [g{g.k}_11, g{g.k}_12]; exact br_bne_byte_f (by decide) {hz}")
            g.load(0x90E, "lw")
            rest = lean_val(g.words[0x148C])
            hz = f"hz_{g.k}"

            def fail_rest(sub):
                sub.branch(0x912, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; exact br_bne_t {hz}")
                err44(sub, 0xB36)
                sub.fail(sub.fail_proof(("prop", hz)))
            g.prop_check(f"{rest} = 0", hz, fail_rest)
            g.branch(0x912, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_bne_f {hz}")
            g.load(0x916, "lw")
            g.block(0x91A, 0x928)
            g.store(0x928, "sw")
            g.store(0x92A, "sw")
            g.jump(0x92C)
        d_next(g)
        stmt, proof = finish(g, 0x4EA, D_KEEP_REGS, D_KEEP_WORDS, set())
        what = f"policy OID {i}" if i < 5 else "none of the OIDs it tests"
        info = {"name": f"sv_dp{i}", "title": f"an extension with {what}",
                "doc": f"From the OID tests at 0x60E back to the loop head at 0x4EA, for an extension with {what}"
                + (": its value must be one `UTF8String`, which fills policy slot " + str(i) + "." if i < 5 else "."),
                "params": params, "stmt": stmt, "proof": proof, "binders": D_BINDERS, "start": 0x60E,
                "import": "C3BootProofs.Proofs.SvData"}
        return g, info
    return gen


def err9b6(sub):
    """The failing exit through 0x9B6: `sw s6, 0x44(sp)`, then 0xB46."""
    sub.store(0x9B6, "sw")
    sub.jump(0x9B8)
    err44(sub, 0xB46)


def stage_dbc1():
    """From the OID tests at 0x60E to 0x81C, for a `BasicConstraints`
    extension: its value is a `SEQUENCE` that fills it."""
    g = Gen("Dbc1")
    params = d_start(g)
    params += [f"(hku : ¬ {oid_is(KU_C)})", f"(heku : ¬ {oid_is(EKU_C)})", f"(hbc : {oid_is(BC_C)})"]
    d_test(g, 0x60E, KU_C, False, "hku")
    d_test(g, 0x6BC, EKU_C, False, "heku")
    d_test(g, 0x78E, BC_C, True, "hbc")
    g.block(0x7A6, 0x7AE)
    g.load(0x7AE, "lw")
    g.store(0x7B0, "sw")
    g.load(0x7B2, "lw")
    g.store(0x7B4, "sw")
    g.store(0x7B6, "sw")
    g.store(0x7B8, "sw")
    g.block(0x7BA, 0x7CA)
    k, ex, rd = g.seqr(0x7CA, 0x1020, 0x1380)
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with er{k} | {t}")
    g.sc.append(("eq", ex, f".ok {t}", [t], f"hr{k}"))
    ks = k

    def fail_seq(sub):
        sub.emit(f"  obtain ⟨z{ks}, -⟩ := Er{ks} er{ks} hr{ks}")
        sub.frame_after(ks, [(0x1020, 16), (0x1388, 8)], {0x1020: ("0", f"z{ks}")})
        sub.load(0x7D2, "lw")
        sub.load_any(0x7D6)
        sub.branch(0x7DA, True, f"by rw [g{sub.k}_8, s{sub.k}.zero]; rfl")
        err9b6(sub)
        sub.fail(sub.fail_proof(("eq", f"hr{ks}")))
    g.fork(fail_seq)
    g.seq_ok(k, 0x1020, 0x1380, t, rd)
    g.load(0x7D2, "lw")
    g.load(0x7D6, "lbu")
    g.branch(0x7DA, False, f"by rw [g{g.k}_8, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{ks})")
    g.block(0x7DE, 0x7F0)
    g.mc(0x7F0, 0x1485, 0x1025, 0xB)
    g.block(0x7F8, 0x802)
    g.load(0x802, "lw")
    g.store(0x804, "sw")
    g.block(0x808, 0x812)
    g.store(0x812, "sb")
    g.block(0x816, 0x818)
    rest = lean_val(g.words[0x138C])
    hz = f"hz_{g.k}"

    def fail_rest(sub):
        sub.branch(0x818, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t {hz}")
        err9b6(sub)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{rest} = 0", hz, fail_rest)
    g.branch(0x818, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f {hz}")
    stmt, proof = finish(g, 0x81C, D_KEEP_REGS + [8, 22], D_KEEP_WORDS | {0x1488, 0x148C}, set())
    info = {"name": "sv_dbc1", "title": "a `BasicConstraints` extension's `SEQUENCE`",
            "doc": "From the OID tests at 0x60E to 0x81C, for a `BasicConstraints` extension: its value is a "
            "`SEQUENCE` that fills it.",
            "params": params, "stmt": stmt, "proof": proof, "binders": D_BINDERS, "start": 0x60E,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


def bc_start(g):
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 27: ("S", 0xA20), 9: ("U", "x9"), 21: ("U", "x21"), 25: ("U", "x25"),
            26: ("U", "x26"), 8: ("S", 0x1320), 22: ("C", 1)}
    words = {0x30: "f30", 0x34: "f34", 0x40: "rem", 0x88: "p0", 0x8C: "L", 0x90: "cur", 0x94: "rest",
             0x1488: "cp", 0x148C: "cl"}
    for i in range(10):
        words[0xA20 + 4 * i] = f"sl{i}"
    for e in range(0x4C, 0x88, 4):
        words[e] = f"w{e:x}"
    return start(g, regs, words, {("cp", "cl"): "c_in"})


BC_BINDERS = LOOP_BINDERS.replace(" : Word}", " cp cl rest : Word}")


def stage_dbc2e():
    """From 0x81C, for an empty `BasicConstraints` sequence: back to the head."""
    g = Gen("Dbc2e")
    params = bc_start(g) + ["(hcl : cl = 0)"]
    g.load(0x81C, "lw")
    g.branch(0x820, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hcl")
    d_next(g)
    stmt, proof = finish(g, 0x4EA, D_KEEP_REGS, D_KEEP_WORDS, set())
    info = {"name": "sv_dbc2e", "title": "an empty `BasicConstraints`",
            "doc": "From 0x81C, for an empty `BasicConstraints` sequence: `cA` is false, back to the loop head.",
            "params": params, "stmt": stmt, "proof": proof, "binders": BC_BINDERS, "start": 0x81C,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


def bc_int_fails(sub, kh, hz, sw_s6):
    """`Der::integer` at 0x876 on the reader at 0x1480, then the checks after it,
    in a part of the stage where every way on fails with `hz`."""
    ki, ex, rd = sub.intc(0x876, 0x1020, 0x1480)
    sub.pinned |= {f"ip{ki}", f"il{ki}", f"ti{ki}", f"hti{ki}"}
    sub.emit(f"  obtain ⟨r{ki}, hr{ki}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    sub.emit(f"  rcases r{ki} with ei{ki} | ⟨ip{ki}, il{ki}⟩")

    def bad(s2):
        s2.emit(f"  obtain ⟨z{ki}, -⟩ := Er{ki} ei{ki} hr{ki}")
        s2.frame_after(ki, [(0x1020, 8), (0x1488, 8)], {0x1020: ("0", f"z{ki}")})
        s2.load(0x87E, "lw")
        s2.branch(0x882, True, f"by rw [g{s2.k}_10, s{s2.k}.zero]; rfl")
        s2.load_any(0x9B2)
        err9b6(s2)
        s2.fail(s2.fail_proof(("prop", hz)))
    sub.fork(bad)
    rp, rl, inp = rd
    sub.emit(f"  obtain ⟨ti{ki}, hti{ki}⟩ := int_ok_elem hr{ki}")
    sub.emit(f"  obtain ⟨p0_{ki}, p4_{ki}⟩ := Ok{ki} ip{ki} il{ki} hr{ki}")
    sub.emit(f"  obtain ⟨d8_{ki}, d12_{ki}⟩ := A{ki} ti{ki} hti{ki}")
    hl = f"BitVec.ofNat 32 (ti{ki}.header + ti{ki}.len)"
    sub.frame_after(ki, [(0x1020, 8), (0x1488, 8)],
                    {0x1020: (f"ip{ki}", f"p0_{ki}"), 0x1024: (f"il{ki}", f"p4_{ki}"),
                     0x1488: (f"({rp}) + {hl}", f"d8_{ki}"), 0x148C: (f"({rl}) - {hl}", f"d12_{ki}")})
    sub.load(0x87E, "lw")
    sub.branch(0x882, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f ({inp}.int_ne hr{ki})")
    sub.load(0x886, "lw")
    rest = lean_val(sub.words[0x148C])
    sub.emit(f"  by_cases hzr{ki} : {rest} = 0")

    def nonempty(s2):
        s2.branch(0x88A, True, f"by rw [g{s2.k}_10, s{s2.k}.zero]; exact br_bne_t hzr{ki}")
        err9b6(s2)
        s2.fail(s2.fail_proof(("prop", hz)))
    sub.emit("  rotate_left")
    sub.fork(nonempty)
    sub.branch(0x88A, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_f hzr{ki}")
    sub.block(0x88E, 0x890)
    return ki


def stage_dbc2():
    """From 0x81C, for a nonempty `BasicConstraints` sequence: `cA` must be
    absent, and an optional `pathLenConstraint` integer must end it."""
    g = Gen("Dbc2")
    params = bc_start(g) + ["(hcl : cl ≠ 0)"]
    g.load(0x81C, "lw")
    g.branch(0x820, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hcl")
    g.load(0x824, "lw")
    g.load_in(0x828, "c_in", "(toNat_pos_of_ne hcl)")
    g.block(0x82C, 0x830)
    hz = f"hz_{g.k}"

    def ca_true(sub):
        sub.pinned.add("hb1")
        sub.emit(f"  have hb1 : M0 cp = BitVec.ofNat 8 1 := Decidable.of_not_not {hz}")
        sub.branch(0x830, False, f"by rw [g{sub.k}_23, g{sub.k}_11]; exact br_bne_byte_f (by decide) hb1")
        sub.block(0x834, 0x83C)
        kb, ex, rd = sub.boolt(0x83C, 0x1480)
        sub.pinned |= {f"tb{kb}", f"htb{kb}", "hb1"}
        sub.emit(f"  obtain ⟨r{kb}, hr{kb}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        sub.emit(f"  rcases r{kb} with eb{kb} | ⟨⟩")

        def bad_bool(s2):
            s2.emit(f"  have g{kb}_10 : reg n{kb} a0 = (derErrByte eb{kb}).zeroExtend 32 := by rw [a0_{kb}, hr{kb}]; rfl")
            s2.regs[10] = ("U", f"(derErrByte eb{kb}).zeroExtend 32")
            s2.frame_after(kb, [(0x1488, 8)], {})
            s2.block(0x844, 0x848)
            s2.block(0x848, 0x84C)
            s2.branch(0x84C, True, f"by rw [g{s2.k}_11, s{s2.k}.zero]; exact br_bne_t (derErr_ff_ne eb{kb})")
            s2.block(0xB52, 0xB54)
            s2.jump(0xB54)
            err9b6(s2)
            s2.fail(s2.fail_proof(("prop", hz)))
        sub.fork(bad_bool)
        sub.emit(f"  have g{kb}_10 : reg n{kb} a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [a0_{kb}, hr{kb}]; rfl")
        sub.regs[10] = ("C", 0xFFFFFFFF)
        rp, rl, inp = rd
        sub.emit(f"  obtain ⟨tb{kb}, htb{kb}⟩ := bool_ok_elem hr{kb}")
        sub.emit(f"  obtain ⟨d8_{kb}, d12_{kb}⟩ := A{kb} tb{kb} htb{kb}")
        hl = f"BitVec.ofNat 32 (tb{kb}.header + tb{kb}.len)"
        cp2, cl2 = f"({rp}) + {hl}", f"({rl}) - {hl}"
        sub.frame_after(kb, [(0x1488, 8)], {0x1488: (cp2, f"d8_{kb}"), 0x148C: (cl2, f"d12_{kb}")})
        sub.slices[(cp2, cl2)] = f"({inp}.restW htb{kb})"
        sub.block(0x844, 0x84C)
        sub.branch(0x84C, False, f"by rw [g{sub.k}_11, s{sub.k}.zero]; decide")
        sub.load(0x850, "lw")
        sub.emit(f"  by_cases hzc : {cl2} = 0")

        def empty_after(s2):
            s2.branch(0x854, True, f"by rw [g{s2.k}_10, s{s2.k}.zero]; exact br_beq_t hzc")
            err44(s2, 0xB46)
            s2.fail(s2.fail_proof(("prop", hz)))
        sub.fork(empty_after)
        sub.branch(0x854, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f hzc")
        sub.load(0x858, "lw")
        sub.load_in(0x85C, f"({inp}.restW htb{kb})", "(toNat_pos_of_ne hzc)")
        sub.block(0x860, 0x862)
        sub.emit(f"  by_cases hb2 : M0 ({cp2}) = BitVec.ofNat 8 2")

        def two(s2):
            s2.branch(0x862, False, f"by rw [g{s2.k}_10, g{s2.k}_11]; exact br_bne_byte_f (by decide) hb2")
            s2.block(0x866, 0x876)
            bc_int_fails(s2, kb, hz, True)
            s2.branch(0x890, True, f"by rw [g{s2.k}_23, g{s2.k}_10]; exact br_beq_byte_t (by decide) hb1")
            err44(s2, 0xB46)
            s2.fail(s2.fail_proof(("prop", hz)))
        sub.fork(two)
        sub.branch(0x862, True, f"by rw [g{sub.k}_10, g{sub.k}_11]; exact br_bne_byte_t (by decide) hb2")
        err9b6(sub)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("M0 cp ≠ BitVec.ofNat 8 1", hz, ca_true)
    g.branch(0x830, True, f"by rw [g{g.k}_23, g{g.k}_11]; exact br_bne_byte_t (by decide) {hz}")
    g.block(0x860, 0x862)
    hz2 = f"hz_{g.k}"

    def not_int(sub):
        sub.branch(0x862, True, f"by rw [g{sub.k}_10, g{sub.k}_11]; exact br_bne_byte_t (by decide) {hz2}")
        err9b6(sub)
        sub.fail(sub.fail_proof(("prop", hz2)))
    g.prop_check("M0 cp = BitVec.ofNat 8 2", hz2, not_int)
    g.branch(0x862, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bne_byte_f (by decide) {hz2}")
    g.block(0x866, 0x876)
    ki, ex, rd = g.intc(0x876, 0x1020, 0x1480)
    g.emit(f"  obtain ⟨r{ki}, hr{ki}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{ki} with ei{ki} | ⟨ip{ki}, il{ki}⟩")
    g.sc.append(("eq", ex, f".ok (ip{ki}, il{ki})", [f"ip{ki}", f"il{ki}"], f"hr{ki}"))

    def bad_int(s2):
        s2.emit(f"  obtain ⟨z{ki}, -⟩ := Er{ki} ei{ki} hr{ki}")
        s2.frame_after(ki, [(0x1020, 8), (0x1488, 8)], {0x1020: ("0", f"z{ki}")})
        s2.load(0x87E, "lw")
        s2.branch(0x882, True, f"by rw [g{s2.k}_10, s{s2.k}.zero]; rfl")
        s2.load_any(0x9B2)
        err9b6(s2)
        s2.fail(s2.fail_proof(("eq", f"hr{ki}")))
    g.fork(bad_int)
    rp, rl, inp = rd
    g.emit(f"  obtain ⟨ti{ki}, hti{ki}⟩ := int_ok_elem hr{ki}")
    L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
    g.sc.append(("eq", f"derElement 2 {L}", f".ok ti{ki}", [f"ti{ki}"], f"hti{ki}"))
    g.emit(f"  obtain ⟨p0_{ki}, p4_{ki}⟩ := Ok{ki} ip{ki} il{ki} hr{ki}")
    g.emit(f"  obtain ⟨d8_{ki}, d12_{ki}⟩ := A{ki} ti{ki} hti{ki}")
    hl = f"BitVec.ofNat 32 (ti{ki}.header + ti{ki}.len)"
    g.frame_after(ki, [(0x1020, 8), (0x1488, 8)],
                  {0x1020: (f"ip{ki}", f"p0_{ki}"), 0x1024: (f"il{ki}", f"p4_{ki}"),
                   0x1488: (f"({rp}) + {hl}", f"d8_{ki}"), 0x148C: (f"({rl}) - {hl}", f"d12_{ki}")})
    g.load(0x87E, "lw")
    g.branch(0x882, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.int_ne hr{ki})")
    g.load(0x886, "lw")
    rest = lean_val(g.words[0x148C])
    hz3 = f"hz_{g.k}"

    def nonempty(sub):
        sub.branch(0x88A, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t {hz3}")
        err9b6(sub)
        sub.fail(sub.fail_proof(("prop", hz3)))
    g.prop_check(f"{rest} = 0", hz3, nonempty)
    g.branch(0x88A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f {hz3}")
    g.block(0x88E, 0x890)
    g.branch(0x890, False, f"by rw [g{g.k}_23, g{g.k}_10]; exact br_beq_byte_f (by decide) {hz}")
    g.jump(0x894)
    d_next(g)
    stmt, proof = finish(g, 0x4EA, D_KEEP_REGS, D_KEEP_WORDS, set())
    info = {"name": "sv_dbc2", "title": "a nonempty `BasicConstraints`",
            "doc": "From 0x81C, for a nonempty `BasicConstraints` sequence: it must not start with `cA`, and "
            "must hold one `pathLenConstraint` integer that ends it.",
            "params": params, "stmt": stmt, "proof": proof, "binders": BC_BINDERS, "start": 0x81C,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info



def stage_dku1():
    """From the OID tests at 0x60E to 0x670, for a `KeyUsage` extension: its
    value starts with a `BIT STRING`."""
    g = Gen("Dku1")
    params = d_start(g)
    params += [f"(hku : {oid_is(KU_C)})"]
    d_test(g, 0x60E, KU_C, True, "hku")
    g.block(0x626, 0x62E)
    g.load(0x62E, "lw")
    g.block(0x630, 0x634)
    g.store(0x634, "sw")
    g.load(0x636, "lw")
    g.store(0x638, "sw")
    g.store(0x63A, "sw")
    g.block(0x63C, 0x646)
    g.store(0x646, "sw")
    g.block(0x648, 0x65A)
    k, ex, rd = g.elem(0x65A, 0x1020, 0x1480, 3)

    def tail(sub):
        sub.load(0x662, "lw")
        sub.branch(0x666, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        err44(sub, 0xB3C)
    g.elem_split(k, ex, 0x1020, 0x1480, rd, tail)
    g.load(0x662, "lw")
    g.branch(0x666, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    g.load(0x66A, "lw")
    g.block(0x66E, 0x670)
    stmt, proof = finish(g, 0x670, D_KEEP_REGS + [8, 10, 11, 12], D_KEEP_WORDS | {0x148C}, set())
    info = {"name": "sv_dku1", "title": "a `KeyUsage` extension's `BIT STRING`",
            "doc": "From the OID tests at 0x60E to 0x670, for a `KeyUsage` extension: its value starts with a "
            "`BIT STRING`.",
            "params": params, "stmt": stmt, "proof": proof, "binders": D_BINDERS, "start": 0x60E,
            "import": "C3BootProofs.Proofs.SvKu"}
    return g, info


def ku_tail(g, last):
    """From 0x93E with the allowed unused bits in `a4`."""
    hz = f"hz_{g.k}u"
    P = f"BitVec.ofNat 32 (kuUnused (M0 ({last}))) = (M0 cp).zeroExtend 32"

    def bad_unused(sub):
        sub.branch(0x93E, True, f"by rw [g{sub.k}_14, g{sub.k}_13]; exact br_bne_t {hz}")
        err44(sub, 0xB44)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(P, hz, bad_unused)
    g.branch(0x93E, False, f"by rw [g{g.k}_14, g{g.k}_13]; exact br_bne_f {hz}")
    g.load(0x942, "lw")
    hz = f"hz_{g.k}"

    def rest(sub):
        sub.branch(0x946, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; exact br_bne_t {hz}")
        err44(sub, 0xB42)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("vrem = 0", hz, rest)
    g.branch(0x946, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_bne_f {hz}")
    g.block(0x94A, 0x94C)
    g.branch(0x94C, False, f"by rw [g{g.k}_12, g{g.k}_11]; exact br_beq_f (ne_one_of h2)")
    g.load_in(0x950, "(c_in.secondIn h2)", "(by decide)")
    hz = f"hz_{g.k}"

    def no_sign(sub):
        sub.branch(0x954, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bge_sext_t (Decidable.of_not_not {hz})")
        err44(sub, 0xB46)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("¬ (M0 (cp + 0x1)).toNat < 0x80", hz, no_sign)
    g.branch(0x954, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bge_sext_f {hz}")
    g.block(0x958, 0x95A)
    g.store(0x95A, "sw")
    d_next(g)


KU_BINDERS = LOOP_BINDERS.replace(" : Word}", " cp kl vrem rest : Word}")


def stage_dku2():
    """From 0x670, the `KeyUsage` bits: at least one byte after the unused-bit
    count, which must match the last byte, nothing after, and
    `digitalSignature` set."""
    g = Gen("Dku2")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 27: ("S", 0xA20), 9: ("U", "x9"), 21: ("U", "x21"), 25: ("U", "x25"),
            26: ("U", "x26"), 8: ("S", 0x1320), 10: ("U", "cp"), 11: ("C", 0x14), 12: ("U", "kl")}
    words = {0x30: "f30", 0x34: "f34", 0x40: "rem", 0x88: "p0", 0x8C: "L", 0x90: "cur", 0x94: "rest",
             0x148C: "vrem"}
    for i in range(10):
        words[0xA20 + 4 * i] = f"sl{i}"
    for e in range(0x4C, 0x88, 4):
        words[e] = f"w{e:x}"
    params = start(g, regs, words, {("cp", "kl"): "c_in"})
    hz = "h2"

    def short(sub):
        sub.emit("  by_cases hk0 : kl = 0")

        def zero(s2):
            s2.branch(0x670, True, f"by rw [g{s2.k}_12, s{s2.k}.zero]; exact br_beq_t hk0")
            err44(s2, 0xB44)
            s2.fail(s2.fail_proof(("prop", hz)))
        sub.fork(zero)
        sub.branch(0x670, False, f"by rw [g{sub.k}_12, s{sub.k}.zero]; exact br_beq_f hk0")
        sub.emit("  have hk1 : kl = BitVec.ofNat 32 0x1 := by")
        sub.emit("    apply BitVec.eq_of_toNat_eq; have := toNat_pos_of_ne hk0; rw [show (BitVec.ofNat 32 0x1).toNat = 1 from rfl]; omega")
        sub.pinned.add("hk1")
        sub.load_in(0x674, "c_in", "(toNat_pos_of_ne hk0)")
        sub.block(0x678, 0x67A)
        sub.branch(0x67A, True, f"by rw [g{sub.k}_12, g{sub.k}_14, hk1]; rfl")
        sub.emit(f"  by_cases hu : (M0 cp).zeroExtend 32 = (0 : Word)")

        def unused0(s2):
            s2.branch(0x896, False, f"by rw [g{s2.k}_13, s{s2.k}.zero]; exact br_bne_f hu")
            s2.jump(0x89A)
            s2.load(0x942, "lw")
            s2.emit("  by_cases hv : vrem = 0")

            def vz(s3):
                s3.branch(0x946, False, f"by rw [g{s3.k}_11, s{s3.k}.zero]; exact br_bne_f hv")
                s3.block(0x94A, 0x94C)
                s3.branch(0x94C, True, f"by rw [g{s3.k}_12, g{s3.k}_11, hk1]; rfl")
                err44(s3, 0xB46)
                s3.fail(s3.fail_proof(("prop", hz)))
            s2.fork(vz)
            s2.branch(0x946, True, f"by rw [g{s2.k}_11, s{s2.k}.zero]; exact br_bne_t hv")
            err44(s2, 0xB42)
            s2.fail(s2.fail_proof(("prop", hz)))
        sub.fork(unused0)
        sub.branch(0x896, True, f"by rw [g{sub.k}_13, s{sub.k}.zero]; exact br_bne_t hu")
        err44(sub, 0xB44)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("2 ≤ kl.toNat", hz, short)
    g.branch(0x670, False, f"by rw [g{g.k}_12, s{g.k}.zero]; exact br_beq_f (ne_zero_of h2)")
    g.load_in(0x674, "c_in", "(by omega)")
    g.block(0x678, 0x67A)
    g.branch(0x67A, False, f"by rw [g{g.k}_12, g{g.k}_14]; exact br_beq_f (ne_one_of h2)")
    g.block(0x67E, 0x682)
    g.block(0x682, 0x684)
    g.branch(0x684, False, f"by rw [g{g.k}_14, s{g.k}.zero]; exact br_beq_f (c_in.lastIn h2).pos_ne")
    g.load_in(0x688, "(c_in.lastIn h2)", "(by decide)")
    lastv = lean_val(g.regs[14])
    lb = lastv[len("(M0 ("):-len(")).zeroExtend 32")]
    g.emit(f"  by_cases hl : M0 ({lb}) = 0")

    def last0(sub):
        sub.branch(0x68C, True, f"by rw [g{sub.k}_14, s{sub.k}.zero, hl]; rfl")
        sub.block(0x93C, 0x93E, {14: (f"BitVec.ofNat 32 (kuUnused (M0 ({lb})))",
                                    "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, svDku293c, upd, ↓reduceIte, aluEval]; "
                                    "exact kuUnused_zero hl")})
        ku_tail(sub, lb)
        sub.exit_here()
    g.fork(last0)
    g.branch(0x68C, False, f"by rw [g{g.k}_14, s{g.k}.zero]; exact br_beq_f (zext_ne_zero hl)")
    k = g.k
    g.block(0x690, 0x6BA, {14: (f"BitVec.ofNat 32 (kuUnused (M0 ({lb})))",
                                "rw [rb{k}, ← kuUnused_ne hl, ← g{p}_14]; rfl")})
    g.jump(0x6BA)
    ku_tail(g, lb)
    stmt, proof = finish(g, 0x4EA, D_KEEP_REGS, D_KEEP_WORDS, set())
    info = {"name": "sv_dku2", "title": "the `KeyUsage` bits",
            "doc": "From 0x670, a `KeyUsage` value's bits: at least one byte after the unused-bit count, which must "
            "match the last byte's trailing zeros (eight for a zero byte), nothing after the `BIT STRING`, and "
            "`digitalSignature` set.",
            "params": params, "stmt": stmt, "proof": proof, "binders": KU_BINDERS, "start": 0x670,
            "import": "C3BootProofs.Proofs.SvKu"}
    return g, info


def stage_deku1():
    """From the OID tests at 0x60E to the inner loop at 0x74A, for an
    `ExtKeyUsage` extension: its value is a `SEQUENCE` that fills it."""
    g = Gen("Deku1")
    params = d_start(g)
    params += [f"(hku : ¬ {oid_is(KU_C)})", f"(heku : {oid_is(EKU_C)})"]
    d_test(g, 0x60E, KU_C, False, "hku")
    d_test(g, 0x6BC, EKU_C, True, "heku")
    g.block(0x6D4, 0x6DC)
    g.load(0x6DC, "lw")
    g.store(0x6DE, "sw")
    g.load(0x6E0, "lw")
    g.store(0x6E2, "sw")
    g.store(0x6E4, "sw")
    g.store(0x6E6, "sw")
    g.block(0x6E8, 0x6F8)
    k, ex, rd = g.seqr(0x6F8, 0x1020, 0x1380)
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with er{k} | {t}")
    g.sc.append(("eq", ex, f".ok {t}", [t], f"hr{k}"))
    ks = k

    def fail_seq(sub):
        sub.emit(f"  obtain ⟨z{ks}, -⟩ := Er{ks} er{ks} hr{ks}")
        sub.frame_after(ks, [(0x1020, 16), (0x1388, 8)], {0x1020: ("0", f"z{ks}")})
        sub.load(0x700, "lw")
        sub.load_any(0x704)
        sub.branch(0x708, True, f"by rw [g{sub.k}_8, s{sub.k}.zero]; rfl")
        err9b6(sub)
        sub.fail(sub.fail_proof(("eq", f"hr{ks}")))
    g.fork(fail_seq)
    g.seq_ok(k, 0x1020, 0x1380, t, rd)
    g.load(0x700, "lw")
    g.load(0x704, "lbu")
    g.branch(0x708, False, f"by rw [g{g.k}_8, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{ks})")
    g.block(0x70C, 0x71E)
    g.mc(0x71E, 0x1485, 0x1025, 0xB)
    g.block(0x726, 0x730)
    g.load(0x730, "lw")
    g.store(0x732, "sw")
    g.block(0x736, 0x740)
    g.store(0x740, "sb")
    rest = lean_val(g.words[0x138C])
    hz = f"hz_{g.k}"

    def fail_rest(sub):
        sub.branch(0x744, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t {hz}")
        sub.block(0xB4A, 0xB4C)
        sub.jump(0xB4C)
        err9b6(sub)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{rest} = 0", hz, fail_rest)
    g.branch(0x744, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f {hz}")
    g.block(0x748, 0x74A)
    stmt, proof = finish(g, 0x74A, D_KEEP_REGS + [8, 22], D_KEEP_WORDS | {0x1488, 0x148C}, set())
    info = {"name": "sv_deku1", "title": "an `ExtKeyUsage` extension's `SEQUENCE`",
            "doc": "From the OID tests at 0x60E to the inner loop at 0x74A, for an `ExtKeyUsage` extension: its "
            "value is a `SEQUENCE` that fills it.",
            "params": params, "stmt": stmt, "proof": proof, "binders": D_BINDERS, "start": 0x60E,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


def eku_start(g):
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 27: ("S", 0xA20), 9: ("U", "x9"), 21: ("U", "x21"), 25: ("U", "x25"),
            26: ("U", "x26"), 8: ("S", 0x1320), 22: ("U", "found")}
    words = {0x30: "f30", 0x34: "f34", 0x40: "rem", 0x88: "p0", 0x8C: "L", 0x90: "cur", 0x94: "rest",
             0x1488: "cp", 0x148C: "cl"}
    for i in range(10):
        words[0xA20 + 4 * i] = f"sl{i}"
    for e in range(0x4C, 0x88, 4):
        words[e] = f"w{e:x}"
    return start(g, regs, words, {("cp", "cl"): "c_in"})


EKU_BINDERS = LOOP_BINDERS.replace(" : Word}", " cp cl rest found : Word}")
CODESIGN = 0x3FCC4820


def stage_deku2():
    """One pass of the `ExtKeyUsage` loop, from 0x74A back to 0x74A: the next
    OID, and whether it is `codeSigning`."""
    g = Gen("Deku2")
    params = eku_start(g) + ["(hcl : cl ≠ 0)", "(SD0 : SvData M0)"]
    g.load(0x74A, "lw")
    g.branch(0x74E, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hcl")
    g.block(0x752, 0x762)

    def tail(sub):
        sub.load(0x76A, "lw")
        sub.branch(0x76E, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
        sub.load_any(0x9B2)
        err9b6(sub)
    k, op, ol = g.oid(0x762, 0x1020, 0x1480, tail)
    g.load(0x76A, "lw")
    g.branch(0x76E, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(op, ol)]}.pos_ne)")
    g.load(0x772, "lw")
    g.block(0x776, 0x780)
    ke = g.seqeq(0x780, op, f"{ol}.toNat", f"BitVec.ofNat 32 0x{CODESIGN:X}", "8", f"(.inl {g.slices[(op, ol)]})",
                 "(.inr ⟨by decide, by decide⟩)", ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
    eq = f"memBytes M0 {op} {ol}.toNat = memBytes M0 (BitVec.ofNat 32 0x{CODESIGN:X}) 8"
    g.emit(f"  have g{ke}_10 : reg n{ke} a0 = if {eq} then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := a0_{ke}")
    g.regs[10] = ("U", f"if {eq} then BitVec.ofNat 32 1 else BitVec.ofNat 32 0")
    g.block(0x788, 0x78C)
    g.jump(0x78C)
    stmt, proof = finish(g, 0x74A, D_KEEP_REGS + [8, 22], D_KEEP_WORDS | {0x1488, 0x148C}, set())
    info = {"name": "sv_deku2", "title": "an `ExtKeyUsage` OID",
            "doc": "One pass of the `ExtKeyUsage` loop, from 0x74A back to 0x74A: the next entry must be an OID, and "
            "the flag in `s6` gains whether it is `codeSigning`.",
            "params": params, "stmt": stmt, "proof": proof, "binders": EKU_BINDERS, "start": 0x74A,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


def stage_deku3():
    """The end of the `ExtKeyUsage` loop at 0x74A: `codeSigning` must have
    appeared; back to the extensions loop's head."""
    g = Gen("Deku3")
    params = eku_start(g) + ["(hcl : cl = 0)"]
    g.load(0x74A, "lw")
    g.branch(0x74E, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hcl")
    g.block(0x92E, 0x932)
    hz = f"hz_{g.k}"

    def none(sub):
        sub.branch(0x932, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not {hz})")
        err44(sub, 0xB46)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("found &&& BitVec.ofNat 32 0x1 ≠ 0", hz, none)
    g.branch(0x932, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f {hz}")
    g.block(0x936, 0x938)
    g.store(0x938, "sw")
    g.jump(0x93A)
    d_next(g)
    stmt, proof = finish(g, 0x4EA, D_KEEP_REGS, D_KEEP_WORDS, set())
    info = {"name": "sv_deku3", "title": "the end of an `ExtKeyUsage` value",
            "doc": "The end of the `ExtKeyUsage` loop at 0x74A: the flag must show `codeSigning`, which sets the "
            "`codeSigning` flag; back to the extensions loop's head.",
            "params": params, "stmt": stmt, "proof": proof, "binders": EKU_BINDERS, "start": 0x74A,
            "import": "C3BootProofs.Proofs.SvData"}
    return g, info


def stage_l7():
    """From the extensions loop's end at 0x4EA to the leaf's signature at 0xA44."""
    g = Gen("L7")
    params = loop_start(g)
    params = [x for x in params if not x.startswith("(xl_in")]
    for e, v in {0x60: "orp", 0x64: "BitVec.ofNat 32 orl", 0x70: "arp", 0x74: "BitVec.ofNat 32 arl",
                 0x7C: "sgp", 0x68: "BitVec.ofNat 32 sgl"}.items():
        g.words[e] = ("U", v)
        params = [x for x in params if not x.startswith(f"(w0_{e:x} ")]
        params.append(f"(w0_{e:x} : memLoad32 n0.mem ({fa(e)}) = {v})")
    params += ["(hrem : rem = 0)", "(or_in : SvIn B orp orl)", "(ar_in : SvIn B arp arl)", "(sg_in : SvIn B sgp sgl)"]
    g.load(0x4EA, "lw")
    g.branch(0x4EC, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hrem")
    for i, (ld, st, br) in enumerate([(0x9C0, 0x9C4, 0x9C6), (0x9CA, 0x9CE, 0x9D0), (0x9D4, 0x9D8, 0x9DA),
                                      (0x9DE, 0x9E2, 0x9E4)]):
        g.load(ld, "lw")
        g.store(st, "sw")
        hz = f"hz_{g.k}"

        def missing(sub, br=br, hz=hz):
            sub.branch(br, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not {hz})")
            sub.block(0xB32, 0xB34)
            sub.jump(0xB34)
            sub.fail(sub.fail_proof(("prop", hz)))
        g.prop_check(f"sl{2 * i} ≠ 0", hz, missing)
        g.branch(br, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f {hz}")
    g.load(0x9E8, "lw")
    g.store(0x9EC, "sw")
    g.block(0x9EE, 0x9F2, {10: ("if BitVec.ult 0 (sl8) then (1 : Word) else 0",
                                "rw [rb{k}]; simp only [runBlock, BInstr.run, svL79ee, upd, aluEval]; "
                                "rw [g{p}_10, s{p}.zero]; rfl")})
    g.load(0x9F2, "lw")
    g.load(0x9F4, "lw")
    g.block(0x9F6, 0x9F8)
    g.block(0x9F8, 0x9FA)
    v = lean_val(g.regs[10])
    hz = f"hz_{g.k}"

    def flags(sub):
        sub.branch(0x9FA, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not {hz})")
        sub.block(0xB32, 0xB34)
        sub.jump(0xB34)
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check(f"{v} ≠ 0", hz, flags)
    g.branch(0x9FA, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f {hz}")
    g.block(0x9FE, 0xA00)
    for ld, st in [(0xA00, 0xA02), (0xA04, 0xA06), (0xA08, 0xA0A), (0xA0C, 0xA0E), (0xA10, 0xA12)]:
        g.load(ld, "lw")
        g.store(st, "sw")
    for ld in (0xA14, 0xA16, 0xA18, 0xA1A):
        g.load(ld, "lw")
    ks = g.sne(0xA1C, "orp", "orl", "arp", "arl", "(.inl or_in)", "(.inl ar_in)")
    hz = f"hz_{ks}"

    def algdiff(sub):
        sub.set_a0(ks, 1, f"ite_eq_right {hz}")
        sub.branch(0xA24, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", hz)))
    g.prop_check("memBytes M0 orp orl = memBytes M0 arp arl", hz, algdiff)
    g.set_a0(ks, 0, f"ite_eq_left {hz}")
    g.branch(0xA24, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0xA26, 0xA2E)
    g.load(0xA2E, "lw")
    g.load(0xA30, "lw")
    k = g.es(0xA32, 0xA20, "sgp", "sgl", "sg_in")
    stmt, proof = finish(g, 0xA44, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                         set(range(0x24, 0x88, 4)) | {0x88, 0x8C, 0x90, 0x94}, set())
    info = {"name": "sv_l7", "title": "the policy and the leaf's signature",
            "doc": "From the extensions loop's end at 0x4EA to 0xA44: all five identity-policy slots are filled, "
            "`KeyUsage` and `ExtKeyUsage` were seen, the outer signature algorithm matches the tbsCertificate's, "
            "and the signature value is an ECDSA signature with 48-byte `r` and `s`.",
            "params": params, "stmt": stmt, "proof": proof,
            "binders": LOOP_BINDERS.replace(" : Word}", " orp arp sgp : Word} {orl arl sgl : Nat}"),
            "start": 0x4EA, "import": "C3BootProofs.Proofs.SvEcdsa"}
    return g, info


L8_BINDERS = ("{B out bp x9 x21 x25 x26 rootp trl sgp : Word} {sr ss : Bytes} "
              + "{" + " ".join(f"w{e:x}" for e in range(0x24, 0x88, 4) if e not in (0x78, 0x7C, 0x80))
              + " : Word} {v : Nat → Word} {n0 : Machine}")


def stage_l8a():
    """From 0xA44 to the intermediates loop at 0xAE2: the parsed leaf's fields."""
    g = Gen("L8a")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 27: ("S", 0xA20), 9: ("U", "x9"), 21: ("U", "x21"), 25: ("U", "x25"), 26: ("U", "x26"),
            20: ("U", "(BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32", "BitVec.ofNat 8 (sr.getD 0 0)")}
    words = {e: f"w{e:x}" for e in range(0x24, 0x88, 4)}
    words.update({0x78: "trl", 0x7C: "sgp", 0x80: "rootp"})
    params = start(g, regs, words, {})
    g.ranges[0xA21] = (48, "BitVec.ofNat 8 (sr.getD j 0)")
    g.ranges[0xA51] = (48, "BitVec.ofNat 8 (ss.getD j 0)")
    params += ["(q0_a21 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 (sr.getD j 0))",
               "(q0_a51 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 (ss.getD j 0))"]
    g.block(0xA44, 0xA54)
    g.mc(0xA54, 0x420, 0xA22, 0x5F)
    g.load(0xA5C, "lw")
    g.block(0xA5E, 0xA62)
    g.block(0xA62, 0xA66)
    g.block(0xA66, 0xA6A)
    g.store(0xA6A, "sb")
    g.store(0xA6E, "sb")
    g.store(0xA72, "sb")
    g.load(0xA76, "lw")
    g.store(0xA78, "sw")
    g.store(0xA7A, "sw")
    for o in range(0xA7C, 0xAA4, 4):
        g.load(o, "lw")
        g.store(o + 2, "sw")
    g.store(0xAA4, "sb")
    g.block(0xAA8, 0xAB4)
    g.mc(0xAB4, 0xD1, 0x420, 0x5F)
    g.store(0xABC, "sw")
    g.store(0xABE, "sb")
    g.assemble_word(0x8C, "trl")
    for o in range(0xAC2, 0xAD2, 4):
        g.load(o, "lw")
        g.store(o + 2, "sw")
    g.store(0xAD2, "sw")
    g.load(0xAD6, "lw")
    g.block(0xAD8, 0xADC)
    g.store(0xADC, "sw")
    g.block(0xADE, 0xAE2)
    stmt, proof = finish(g, 0xAE2, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                         set(range(0x24, 0x134, 4)), set(g.bytes))
    info = {"name": "sv_l8a", "title": "the parsed leaf",
            "doc": "From 0xA44 to the intermediates loop at 0xAE2: `sigstore::verify` copies the leaf's fields, "
            "with `r` and `s`, into its `Leaf` at offset 0x88 of the frame.",
            "params": params, "stmt": stmt, "proof": proof, "binders": L8_BINDERS, "start": 0xA44,
            "import": "C3BootProofs.Proofs.SvFail"}
    return g, info


def i_start(g):
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 27: ("S", 0xA20), 9: ("U", "x9"), 21: ("U", "x21"), 25: ("U", "il"), 26: ("U", "x26"),
            20: ("U", "c")}
    words = {e: f"w{e:x}" for e in range(0x24, 0x134, 4)}
    words.update({0x5C: "ip", 0x7C: "q"})
    params = start(g, regs, words, {})
    return params


I_BINDERS = ("{B out bp x9 x21 x26 il c q ip subj slen : Word} "
             + "{" + " ".join(f"w{e:x}" for e in range(0x24, 0x134, 4) if e not in (0x5C, 0x7C))
             + " : Word} {v : Nat → Word} {n0 : Machine}")
I_KEEP = set(range(0x24, 0x134, 4))


def i_entry(g):
    """From 0xAE2 to the comparison at 0xB06, for an entry with a subject."""
    g.branch(0xAE2, True, f"by rw [g{g.k}_20, s{g.k}.zero]; exact br_bne_t hc")
    g.load(0xAEA, "lw")
    g.load_mem(0xAEC, "subj", "hsubj", "es_in", "a_subj")
    hz = f"hz_{g.k}"

    def null(sub):
        sub.branch(0xAF0, False, f"by rw [g{sub.k}_22, s{sub.k}.zero]; exact br_bne_f (Decidable.of_not_not {hz})")
        sub.jump(0xAF4)
        sub.fail(sub.fail_proof(("prop", hz)), "sv_fail_2a82")
    g.prop_check("subj ≠ 0", hz, null)
    g.branch(0xAF0, True, f"by rw [g{g.k}_22, s{g.k}.zero]; exact br_bne_t {hz}")
    g.load(0xAF8, "lw")
    g.load_mem(0xAFA, "slen", "hslen", "el_in", "a_slen")
    g.block(0xAFE, 0xB02)
    g.load(0xB02, "lw")
    g.block(0xB04, 0xB06)
    return g.seqeq(0xB06, "subj", "slen.toNat", "ip", "il.toNat", "(.inl s_in)", "(.inl i_in)",
                   f"(by rw [g{g.k}_13, ofNat_toNat_self])", f"(by rw [g{g.k}_11, ofNat_toNat_self])")


I_PARAMS = ["(hc : c ≠ 0)", "(hsubj : memLoad32 M0 (q + 0xFFFFFFFC) = subj)",
            "(hslen : memLoad32 M0 (q + 0x0) = slen)", "(es_in : SvIn B (q + 0xFFFFFFFC) 4)",
            "(el_in : SvIn B (q + 0x0) 4)",
            "(a_subj : (q + 0xFFFFFFFC).toNat % 4 = 0)", "(a_slen : (q + 0x0).toNat % 4 = 0)",
            "(s_in : SvIn B subj slen.toNat)", "(i_in : SvIn B ip il.toNat)"]
I_EQ = "memBytes M0 subj slen.toNat = memBytes M0 ip il.toNat"


def stage_imiss():
    """One pass of the intermediates loop, from 0xAE2 back to it, for an entry
    whose subject isn't the leaf's issuer."""
    g = Gen("Imiss")
    params = i_start(g) + I_PARAMS + [f"(hm : ¬ {I_EQ})"]
    ke = i_entry(g)
    g.set_a0(ke, 0, "ite_eq_right hm")
    g.block(0xB0E, 0xB10)
    g.block(0xB10, 0xB14)
    g.store(0xB14, "sw")
    g.branch(0xB16, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0xAE2, [2, 3, 4, 9, 18, 19, 20, 21, 25, 26, 27], I_KEEP, set())
    info = {"name": "sv_imiss", "title": "an intermediate that didn't issue the leaf",
            "doc": "One pass of the intermediates loop, from 0xAE2 back to it, for a listed intermediate whose "
            "subject isn't the leaf's issuer.",
            "params": params, "stmt": stmt, "proof": proof, "binders": I_BINDERS, "start": 0xAE2,
            "import": "C3BootProofs.Proofs.SvFail"}
    return g, info


def stage_ihit():
    """The intermediates loop's end at the intermediate that issued the leaf."""
    g = Gen("Ihit")
    params = i_start(g) + I_PARAMS + [f"(hm : {I_EQ})"]
    ke = i_entry(g)
    g.set_a0(ke, 1, "ite_eq_left hm")
    g.block(0xB0E, 0xB10)
    g.block(0xB10, 0xB14)
    g.store(0xB14, "sw")
    g.branch(0xB16, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load(0xB18, "lw")
    g.block(0xB1A, 0xB20)
    kn = g.sne(0xB20, "ip", "il.toNat", "subj", "slen.toNat", "(.inl i_in)", "(.inl s_in)",
               f"(by rw [g{g.k}_11, ofNat_toNat_self])", f"(by rw [g{g.k}_13, ofNat_toNat_self])")
    g.set_a0(kn, 0, "ite_eq_left hm.symm")
    g.branch(0xB28, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0xB56, [2, 3, 4, 8, 9, 18, 19, 21, 22, 23, 25, 26, 27], I_KEEP, set())
    info = {"name": "sv_ihit", "title": "the intermediate that issued the leaf",
            "doc": "The intermediates loop's end, from 0xAE2 to 0xB56, at a listed intermediate whose subject is the "
            "leaf's issuer.",
            "params": params, "stmt": stmt, "proof": proof, "binders": I_BINDERS, "start": 0xAE2,
            "import": "C3BootProofs.Proofs.SvFail"}
    return g, info


def stage_iend():
    """The intermediates loop with no entries left: no intermediate issued the leaf."""
    g = Gen("Iend")
    params = i_start(g) + ["(hc : c = 0)"]
    hz = "hf"

    def none(sub):
        sub.branch(0xAE2, False, f"by rw [g{sub.k}_20, s{sub.k}.zero]; exact br_bne_f hc")
        sub.jump(0xAE6)
        sub.fail(sub.fail_proof(("prop", hz)), "sv_fail_2a82")
    g.prop_check("False", hz, none)
    stmt, _ = finish(g, 0xAE2, [2], set(), set())
    g.emit("  exact hf.elim")
    info = {"name": "sv_iend", "title": "no intermediate left",
            "doc": "The intermediates loop at 0xAE2 with no entries left: no listed intermediate issued the leaf, "
            "and `sigstore::verify` fails.",
            "params": params, "stmt": stmt, "proof": "", "binders": I_BINDERS, "start": 0xAE2,
            "import": "C3BootProofs.Proofs.SvFail"}
    return g, info


# --- after the leaf's signature check -------------------------------------------

DPV_WORDS = [e for e in range(0x24, 0x134, 4) if e not in (0x74, 0x78)]
DPV_PAIRS = [(0x48, 0x34), (0x44, 0x30), (0x40, 0x2C), (0x3C, 0x28), (0x38, 0x24)]
DPV_BINDERS = ("{B out bp x21 x26 pv tsp tsl " + " ".join(f"e{i}p e{i}l" for i in range(5)) + " : Word} "
               + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def seq_fail_2c60(sub, k, oc, dc):
    """`Der::sequence`'s failing case at 0xE80: the null address, `lw`, `lbu`,
    `bnez` not taken, and `j` to the exit at 0x2C60."""
    sub.emit(f"  obtain ⟨z{k}, -⟩ := Er{k} er{k} hr{k}")
    sub.frame_after(k, [(oc, 16), (dc + 8, 8)], {oc: ("0", f"z{k}")})
    sub.load(0xE88, "lw")
    sub.load_any(0xE8C)
    sub.branch(0xE90, False, f"by rw [g{sub.k}_9, s{sub.k}.zero]; rfl")
    sub.jump(0xE92)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def stage_dpv():
    """From 0xDE6, after `p384_verify_prehash`: its result, the five policy
    values against the trust root's, and `Der::sequence` on the timestamp."""
    g = Gen("Dpv")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 10: ("U", "pv")}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    params = start(g, regs, words, {("tsp", "tsl"): "ts_in"})
    for i, (pe, le) in enumerate(DPV_PAIRS):
        params += [f"(he{i}p : memLoad32 M0 (w80 + 0x{8 * i:X}) = e{i}p)",
                   f"(he{i}l : memLoad32 M0 (w80 + 0x{8 * i + 4:X}) = e{i}l)",
                   f"(he{i}p_in : SvIn B (w80 + 0x{8 * i:X}) 4)", f"(he{i}l_in : SvIn B (w80 + 0x{8 * i + 4:X}) 4)",
                   f"(ae{i}p : (w80 + 0x{8 * i:X}).toNat % 4 = 0)", f"(ae{i}l : (w80 + 0x{8 * i + 4:X}).toNat % 4 = 0)",
                   f"(p{i}_in : SvRo B w{pe:x} w{le:x}.toNat)", f"(e{i}_in : SvRo B e{i}p e{i}l.toNat)"]
    params += ["(htsp : memLoad32 M0 (bp + 0x8) = tsp)", "(htsl : memLoad32 M0 (bp + 0xC) = tsl)",
               "(htsp_in : SvIn B (bp + 0x8) 4)", "(htsl_in : SvIn B (bp + 0xC) 4)",
               "(atsp : (bp + 0x8).toNat % 4 = 0)", "(atsl : (bp + 0xC).toNat % 4 = 0)"]

    def zero(sub):
        sub.branch(0xDE6, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not hpv)")
        sub.fail(sub.fail_proof(("prop", "hpv")), "sv_fail_ee2")
    g.prop_check("pv ≠ 0", "hpv", zero)
    g.branch(0xDE6, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hpv")
    for i, (pe, le) in enumerate(DPV_PAIRS):
        at = 0xDE8 + 0x14 * i
        g.load(at, "lw")
        g.load_mem(at + 2, f"e{i}p", f"he{i}p", f"he{i}p_in", f"ae{i}p")
        g.load_mem(at + 4, f"e{i}l", f"he{i}l", f"he{i}l_in", f"ae{i}l")
        g.load(at + 6, "lw")
        g.load(at + 8, "lw")
        ke = g.seqeq(at + 0xA, f"w{pe:x}", f"w{le:x}.toNat", f"e{i}p", f"e{i}l.toNat", f"p{i}_in", f"e{i}_in",
                     ha3=f"(by rw [g{g.k}_13, ofNat_toNat_self])", ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
        hq = f"hq{i}"

        def ne(sub, ke=ke, at=at, hq=hq):
            sub.set_a0(ke, 0, f"ite_eq_right {hq}")
            sub.branch(at + 0x12, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
            sub.fail(sub.fail_proof(("prop", hq)), "sv_fail_ef0")
        g.prop_check(f"memBytes M0 w{pe:x} w{le:x}.toNat = memBytes M0 e{i}p e{i}l.toNat", hq, ne)
        g.set_a0(ke, 1, f"ite_eq_left {hq}")
        g.branch(at + 0x12, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0xE4C, 0xE4E)
    g.load_mem(0xE4E, "tsp", "htsp", "htsp_in", "atsp")
    g.load_mem(0xE50, "tsl", "htsl", "htsl_in", "atsl")
    g.block(0xE52, 0xE5A)
    g.store(0xE5A, "sw")
    g.store(0xE5C, "sw")
    g.store(0xE5E, "sw")
    g.store(0xE60, "sw")
    g.block(0xE62, 0xE6C)
    g.store(0xE6C, "sw")
    g.store(0xE6E, "sw")
    g.block(0xE70, 0xE80)
    k, ex, rd = g.seqr(0xE80, 0xA20, 0x1320)
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with er{k} | {t}")
    g.sc.append(("eq", ex, f".ok {t}", [t], f"hr{k}"))
    g.fork(lambda sub: seq_fail_2c60(sub, k, 0xA20, 0x1320))
    g.seq_ok(k, 0xA20, 0x1320, t, rd)
    g.load(0xE88, "lw")
    g.load(0xE8C, "lbu")
    g.branch(0xE90, True, f"by rw [g{g.k}_9, s{g.k}.zero]; exact br_bne_t ({rd[2]}.ok_ne hr{k})")
    stmt, proof = finish(g, 0xE96, [2, 3, 4, 8, 9, 18, 19, 20, 21, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_dpv", "title": "the leaf's signature result and the trust root's policy values",
            "doc": "From 0xDE6 to 0xE96: `p384_verify_prehash`'s result must be nonzero, the leaf's five policy "
            "values must equal the trust root's, and the timestamp must start with a DER sequence.",
            "params": params, "stmt": stmt, "proof": proof, "binders": DPV_BINDERS, "start": 0xDE6,
            "import": "C3BootProofs.Proofs.SvFail2"}
    return g, info


TS_WORDS = DPV_WORDS
TS_BINDERS = ("{B out bp x21 x26 tsp tsl : Word} {tl : DerTlv} "
              + "{" + " ".join(f"w{e:x}" for e in TS_WORDS if e not in (0x64, 0x68)) + " : Word} {v : Nat → Word} {n0 : Machine}")


def ts_scalar_fail(sub, a, reg):
    """After a failing `der::scalar::<32>`: `lbu`, `lbu`, `beqz` not taken, `mv s0`, and `j` to 0x2C60."""
    sub.load(a, "lbu")
    sub.load(a + 4, "lbu")
    sub.branch(a + 8, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.block(a + 0xA, a + 0xC)
    sub.jump(a + 0xC)


def stage_ts1():
    """From 0xE96 to 0xFBA: the timestamp signature's `r` and `s`."""
    g = Gen("Ts1")
    cp = "(tsp) + BitVec.ofNat 32 tl.header"
    cl = "BitVec.ofNat 32 tl.len"
    byte = f"({cl}).extractLsb' 0 8"
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 20: ("S", 0x1320),
            9: ("U", cp), 8: ("U", f"({byte}).zeroExtend 32", byte)}
    words = {e: f"w{e:x}" for e in TS_WORDS}
    words.update({0x64: "tsl", 0x68: "tsp", 0xA20: cp, 0xA24: cl, 0xA28: cp, 0xA2C: cl, 0x1320: "tsp",
                  0x1324: "tsl", 0x1328: "(tsp) + BitVec.ofNat 32 (tl.header + tl.len)",
                  0x132C: "(tsl) - BitVec.ofNat 32 (tl.header + tl.len)"})
    params = start(g, regs, words, {})
    g.bytes[0xA24] = byte
    params += [f"(b0_a24 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = {byte})",
               "(ts_in : SvIn B tsp tsl.toNat)", "(ht : derElement 0x30 (memBytes M0 tsp tsl.toNat) = .ok tl)"]
    g.slices[(cp, cl)] = "(ts_in.contentW ht)"
    g.block(0xE96, 0xEA4)
    g.mc(0xEA4, 0x325, 0xA25, 0xB)
    g.load(0xEAC, "lw")
    g.store(0xEB0, "sw")
    g.store(0xEB4, "sb")
    g.word_of_bytes(0x324, cl)
    g.block(0xEB8, 0xEBA)
    rem = "(tsl) - BitVec.ofNat 32 (tl.header + tl.len)"

    def trailing(sub):
        sub.branch(0xEBA, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f hrem")
        sub.jump(0xEBC)
        sub.fail(sub.fail_proof(("prop", "hrem")), "sv_fail_2c60")
    g.prop_check(f"{rem} = 0", "hrem", trailing)
    g.branch(0xEBA, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hrem")
    g.block(0xEC0, 0xECA)
    k1 = g.ds32(0xECA, 0xA20, 0x320, lambda sub: ts_scalar_fail(sub, 0xED2, 22))
    g.load(0xED2, "lbu")
    g.load(0xED6, "lbu")
    g.branch(0xEDA, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0xEFA, 0xF0C)
    g.mc(0xF0C, 0x1020, 0xA22, 0x1F)
    g.block(0xF14, 0xF1E)
    k2 = g.ds32(0xF1E, 0xA20, 0x320, lambda sub: ts_scalar_fail(sub, 0xF26, 9))
    g.load(0xF26, "lbu")
    g.load(0xF2A, "lbu")
    g.branch(0xF2E, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0xF36, 0xF44)
    g.mc(0xF44, 0x420, 0xA22, 0x1F)
    g.load(0xF4C, "lw")
    rem2 = lean_val(g.words[0x32C])

    def trailing2(sub):
        sub.branch(0xF50, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f hrem2")
        sub.jump(0xF52)
        sub.fail(sub.fail_proof(("prop", "hrem2")), "sv_fail_2c60")
    g.prop_check(f"{rem2} = 0", "hrem2", trailing2)
    g.branch(0xF50, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hrem2")
    g.block(0xF56, 0xF68)
    g.mc(0xF68, 0x1480, 0x1020, 0x1F)
    g.block(0xF70, 0xF7E)
    g.mc(0xF7E, 0x1380, 0x420, 0x1F)
    g.block(0xF86, 0xF94)
    g.mc(0xF94, 0x139, 0x1480, 0x1F)
    g.block(0xF9C, 0xFAA)
    g.mc(0xFAA, 0x159, 0x1380, 0x1F)
    g.store(0xFB2, "sb")
    g.store(0xFB6, "sb")
    stmt, proof = finish(g, 0xFBA, [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_ts1", "title": "the timestamp signature's scalars",
            "doc": "From 0xE96 to 0xFBA: `sigstore::verify` reads the timestamp signature's `r` and `s` with "
            "`der::scalar::<32>` and copies them to offsets 0x138 and 0x158 of the frame.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TS_BINDERS, "start": 0xE96,
            "import": "C3BootProofs.Proofs.SvTs"}
    return g, info


TSA_BINDERS = ("{B out bp x21 x26 c0p c0l : Word} "
               + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def tsa_read_fail(sub, k, off, dc):
    """A failing read into 0x420: the null address, `lw`, `lbu`, `beqz` to 0x2C60."""
    sub.emit(f"  obtain ⟨z{k}, -⟩ := Er{k} er{k} hr{k}")
    sub.frame_after(k, [(0x420, 16), (dc + 8, 8)], {0x420: ("0", f"z{k}")})
    sub.load(off + 8, "lw")
    sub.load_any(off + 0xC)
    sub.branch(off + 0x10, True, f"by rw [g{sub.k}_9, s{sub.k}.zero]; rfl")
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa_read(g, off, dc, kind="seq"):
    """`Der::sequence`, `Der::set`, or `Der::nested` into 0x420 at `off`, split
    on its result, then `lw s1`, `lbu s0`, and `beqz s1` not taken. Returns
    (k, the element's name, the reader)."""
    if kind == "seq":
        k, ex, rd = g.nestr(off, 0x420, dc, "sv_seqF", 0x30)
    elif kind == "set":
        k, ex, rd = g.nestr(off, 0x420, dc, "sv_setF", 0x31)
    else:
        k, ex, rd = g.nestr(off, 0x420, dc, "sv_nestF", kind, f" g{g.k}_12 (by decide)")
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with er{k} | {t}")
    g.sc.append(("eq", ex, f".ok {t}", [t], f"hr{k}"))
    g.fork(lambda sub: tsa_read_fail(sub, k, off, dc))
    g.seq_ok(k, 0x420, dc, t, rd)
    g.load(off + 8, "lw")
    g.load(off + 0xC, "lbu")
    g.branch(off + 0x10, False, f"by rw [g{g.k}_9, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    return k, t, rd


def tsa_rest0(g, at, hname, target, reg=10):
    """`bnez` at `at` on a reader's length in `reg`, which must be zero; the
    failing branch goes to `target`: 0x2838 (`s0 = 1`) or 0x2C60."""
    rem = lean_val(g.regs[reg])

    def fail(sub):
        sub.branch(at, True, f"by rw [g{sub.k}_{reg}, s{sub.k}.zero]; exact br_bne_t {hname}")
        if target == 0x2838:
            sub.block(0x2838, 0x283A)
            sub.jump(0x283A)
        sub.fail(sub.fail_proof(("prop", hname)), "sv_fail_2c60")
    g.prop_check(f"{rem} = 0", hname, fail)
    g.branch(at, False, f"by rw [g{g.k}_{reg}, s{g.k}.zero]; exact br_bne_f {hname}")


def stage_tsa1():
    """From 0x2034 to 0x21A0: the timestamp response, its status, and the
    token's signedData OID."""
    g = Gen("Tsa1")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20)}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    params = start(g, regs, words, {("c0p", "c0l"): "c0_in"})
    params += ["(hc0p : memLoad32 M0 (bp + 0x20) = c0p)", "(hc0l : memLoad32 M0 (bp + 0x24) = c0l)",
               "(hc0p_in : SvIn B (bp + 0x20) 4)", "(hc0l_in : SvIn B (bp + 0x24) 4)",
               "(ac0p : (bp + 0x20).toNat % 4 = 0)", "(ac0l : (bp + 0x24).toNat % 4 = 0)"]
    g.block(0x2034, 0x2036)
    g.load_mem(0x2036, "c0p", "hc0p", "hc0p_in", "ac0p")
    g.load_mem(0x2038, "c0l", "hc0l", "hc0l_in", "ac0l")
    g.block(0x203A, 0x2046)
    for o in (0x2046, 0x2048, 0x204A, 0x204C):
        g.store(o, "sw")
    g.block(0x204E, 0x205A)
    k1, t1, rd1 = tsa_read(g, 0x205A, 0x1608)
    g.block(0x206E, 0x207C)
    g.mc(0x207C, 0x161D, 0x425, 0xB)
    g.block(0x2084, 0x208E)
    g.load(0x208E, "lw")
    g.store(0x2092, "sw")
    g.store(0x2096, "sb")
    g.word_of_bytes(0x161C, f"BitVec.ofNat 32 {t1}.len")
    tsa_rest0(g, 0x209A, "hrest0", 0x2838)
    g.block(0x209E, 0x20AA)
    k2, t2, rd2 = tsa_read(g, 0x20AA, 0x1618)
    g.block(0x20BE, 0x20CC)
    g.mc(0x20CC, 0x162D, 0x425, 0xB)
    g.block(0x20D4, 0x20DC)
    g.store(0x20DC, "sw")
    g.block(0x20E0, 0x20EA)
    g.store(0x20EA, "sb")
    g.word_of_bytes(0x162C, f"BitVec.ofNat 32 {t2}.len")
    g.block(0x20EE, 0x20F8)
    tsa_iis(g, 0x20F8, 0x1628, 0x2100)
    g.load(0x2112, "lw")
    tsa_rest0(g, 0x2116, "hrest1", 0x2C60)
    g.block(0x211A, 0x2126)
    k3, t3, rd3 = tsa_read(g, 0x2126, 0x1618)
    g.block(0x213A, 0x2148)
    g.mc(0x2148, 0x163D, 0x425, 0xB)
    g.block(0x2150, 0x215A)
    g.load(0x215A, "lw")
    g.store(0x215E, "sw")
    g.store(0x2162, "sb")
    g.word_of_bytes(0x163C, f"BitVec.ofNat 32 {t3}.len")
    tsa_rest0(g, 0x2166, "hrest2", 0x2838)
    g.block(0x216A, 0x2176)
    k, op, ol = g.oid(0x2176, 0x420, 0x1638, tsa_oid_tail, "sv_fail_2c60")
    g.load(0x217E, "lw")
    g.branch(0x2182, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(op, ol)]}.pos_ne)")
    g.load(0x2186, "lw")
    g.block(0x218A, 0x2194)
    ks = g.sne(0x2194, op, f"{ol}.toNat", "BitVec.ofNat 32 0x3FCC4859", "9", f"(.inl {g.slices[(op, ol)]})",
               "(.inr ⟨by decide, by decide⟩)", ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
    eq = f"memBytes M0 {op} {ol}.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4859) 9"
    g.prop_check(eq, "hsd", lambda sub: tsa_ne_fail(sub, ks, 0x219C, "hsd"))
    g.set_a0(ks, 0, "ite_eq_left hsd")
    g.branch(0x219C, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0x21A0, [2, 3, 4, 18, 19, 20, 21, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tsa1", "title": "the timestamp response's status and content type",
            "doc": "From 0x2034 to 0x21A0: the timestamp response is a sequence with nothing after it, its status "
            "is a sequence holding only `INTEGER 0` (granted), and its token is a `ContentInfo` whose content "
            "type is signedData.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSA_BINDERS, "start": 0x2034,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


def tsa_ii_fail(sub, k, dc, err, at=0x2100, ne=None):
    """`Der::integer_is` failing: an error (`a0 = 1`) or a different value. The
    result's tests start at `at`; `ne` is where a different value branches when
    it isn't 0x2C60 directly (0x29A6)."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    sub.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x{1 if err else 0:X} := a0_{k}")
    sub.regs[10] = ("C", 1 if err else 0)
    if not err:
        sub.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x0 := by rw [a1_{k}]; rfl")
        sub.regs[11] = ("C", 0)
    sub.frame_after(k, [(dc + 8, 8)], {})
    tsa_ii_tests(sub, at, err, ne)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa_ii_tests(g, at, fail, ne):
    """`andi a0, a0, 1`, `mv s0, a1`, `bnez a0`, then the test of the value: at
    0x2100 `andi a0, s0, 1`, `li s0, 0x18`, `beqz a0`; elsewhere `andi s0, s0, 1`
    and `beqz s0` to `ne`."""
    g.block(at, at + 4)
    if fail is True:
        g.branch(at + 4, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        return
    g.branch(at + 4, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    if ne is None:
        g.block(at + 8, at + 0xE)
        br, reg = at + 0xE, 10
    else:
        g.block(at + 8, at + 0xA)
        br, reg = at + 0xA, 8
    if fail is False:
        g.branch(br, True, f"by rw [g{g.k}_{reg}, s{g.k}.zero]; decide")
        if ne is not None:
            g.block(ne, ne + 2)
            g.jump(ne + 2)
        return
    g.branch(br, False, f"by rw [g{g.k}_{reg}, s{g.k}.zero]; decide")


def tsa_iis(g, off, dc, at, ne=None):
    """`Der::integer_is` at `off` on the reader at `dc`, which must hold the
    value in `a1`, then its tests from `at`."""
    k, ex, rd = g.iis(off, dc)
    rp, rl, inp = rd
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with b{k} | (_ | _)")
    g.sc.append(("eq", ex, ".ok true", [], f"hr{k}"))
    g.fork(lambda sub: tsa_ii_fail(sub, k, dc, True, at, ne))
    g.fork(lambda sub: tsa_ii_fail(sub, k, dc, False, at, ne))
    g.emit(f"  obtain ⟨te{k}, hte{k}⟩ := ii_ok_elem hr{k}")
    g.sc.append(("eq", f"derElement 2 (memBytes M0 ({rp}) ({rl}).toNat)", f".ok te{k}", [f"te{k}"], f"hte{k}"))
    g.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} te{k} hte{k}")
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    g.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x0 := a0_{k}")
    g.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x1 := by rw [a1_{k}]; rfl")
    g.regs[10] = ("C", 0)
    g.regs[11] = ("C", 1)
    hl = f"BitVec.ofNat 32 (te{k}.header + te{k}.len)"
    g.frame_after(k, [(dc + 8, 8)], {dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")})
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hte{k})"
    tsa_ii_tests(g, at, None, ne)
    return k


def tsa_oid_tail(sub, lw_off=0x217E):
    """`Der::oid` failing: `lw`, `beqz` to 0x2994, `lbu s0`, `j` to 0x2C60."""
    sub.load(lw_off, "lw")
    sub.branch(lw_off + 4, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.load_any(0x2994)
    sub.jump(0x2998)


def tsa_ne_fail(sub, ks, at, hname):
    """`<[u8]>::ne` true at `ks`: `bnez` to 0x29A6, `s0 = 0x18`, `j` to 0x2C60."""
    sub.set_a0(ks, 1, f"ite_eq_right {hname}")
    sub.branch(at, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.block(0x29A6, 0x29A8)
    sub.jump(0x29A8)
    sub.fail(sub.fail_proof(("prop", hname)), "sv_fail_2c60")


TSA2_BINDERS = ("{B out bp x21 x26 cip cil : Word} "
                + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def tsa_issha_fail(sub, k, dc, err, at=0x2298):
    """`tsa::is_sha256` failing: an error, or another algorithm. Its tests start at `at`."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    sub.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x{1 if err else 0:X} := a0_{k}")
    sub.regs[10] = ("C", 1 if err else 0)
    if not err:
        sub.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x0 := by rw [a1_{k}]; rfl")
        sub.regs[11] = ("C", 0)
    sub.frame_after(k, [(dc + 8, 8)], {})
    tsa_ii_tests(sub, at, err, None)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def stage_tsa2():
    """From 0x21A0 to 0x2316: the token's `[0]` content, the `SignedData`, its
    version, its digest algorithm, and the encapsulated content's type."""
    g = Gen("Tsa2")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20)}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    words.update({0x1640: "cip", 0x1644: "cil"})
    params = start(g, regs, words, {("cip", "cil"): "ci_in"}) + ["(D0 : SvData M0)"]
    g.block(0x21A0, 0x21B0)
    k1, t1, rd1 = tsa_read(g, 0x21B0, 0x1638, 0xA0)
    g.block(0x21C4, 0x21D2)
    g.mc(0x21D2, 0x164D, 0x425, 0xB)
    g.block(0x21DA, 0x21E4)
    g.load(0x21E4, "lw")
    g.store(0x21E8, "sw")
    g.block(0x21EC, 0x21F6)
    g.store(0x21F6, "sb")
    g.word_of_bytes(0x164C, f"BitVec.ofNat 32 {t1}.len")
    tsa_rest0(g, 0x21FA, "hrest0", 0x2838)
    g.block(0x21FE, 0x220A)
    k2, t2, rd2 = tsa_read(g, 0x220A, 0x1648)
    g.block(0x221E, 0x2228)
    g.mc(0x2228, 0x2A5, 0x425, 0xB)
    g.load(0x2230, "lw")
    g.store(0x2234, "sw")
    g.store(0x2238, "sb")
    g.word_of_bytes(0x2A4, f"BitVec.ofNat 32 {t2}.len")
    tsa_rest0(g, 0x223C, "hrest1", 0x2838)
    g.block(0x2240, 0x2244)
    tsa_iis(g, 0x2244, 0x2A0, 0x224C, 0x29A6)
    g.block(0x225A, 0x2260)
    k3, t3, rd3 = tsa_read(g, 0x2260, 0x2A0, "set")
    g.block(0x2274, 0x227E)
    g.mc(0x227E, 0x2C5, 0x425, 0xB)
    g.store(0x2286, "sw")
    g.store(0x228A, "sb")
    g.word_of_bytes(0x2C4, f"BitVec.ofNat 32 {t3}.len")
    g.block(0x228E, 0x2290)
    k, ex, rd = g.issha(0x2290, 0x2C0)
    rp, rl, inp = rd
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with b{k} | (_ | _)")
    g.sc.append(("eq", ex, ".ok true", [], f"hr{k}"))
    g.fork(lambda sub: tsa_issha_fail(sub, k, 0x2C0, True))
    g.fork(lambda sub: tsa_issha_fail(sub, k, 0x2C0, False))
    g.emit(f"  obtain ⟨te{k}, hte{k}⟩ := isSha256Of_ok_elem hr{k}")
    g.sc.append(("eq", f"derElement 0x30 (memBytes M0 ({rp}) ({rl}).toNat)", f".ok te{k}", [f"te{k}"], f"hte{k}"))
    g.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} te{k} hte{k}")
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    g.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x0 := a0_{k}")
    g.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x1 := by rw [a1_{k}]; rfl")
    g.regs[10] = ("C", 0)
    g.regs[11] = ("C", 1)
    hl = f"BitVec.ofNat 32 (te{k}.header + te{k}.len)"
    g.frame_after(k, [(0x2C8, 8)], {0x2C8: (f"({rp}) + {hl}", f"d8_{k}"), 0x2CC: (f"({rl}) - {hl}", f"d12_{k}")})
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hte{k})"
    tsa_ii_tests(g, 0x2298, None, None)
    g.load(0x22AA, "lw")
    tsa_rest0(g, 0x22AE, "hrest2", 0x2C60)
    g.block(0x22B2, 0x22B8)
    k4, t4, rd4 = tsa_read(g, 0x22B8, 0x2A0)
    g.block(0x22CC, 0x22D6)
    g.mc(0x22D6, 0x2E5, 0x425, 0xB)
    g.store(0x22DE, "sw")
    g.store(0x22E2, "sb")
    g.word_of_bytes(0x2E4, f"BitVec.ofNat 32 {t4}.len")
    g.block(0x22E6, 0x22EC)
    k, op, ol = g.oid(0x22EC, 0x420, 0x2E0, lambda sub: tsa_oid_tail(sub, 0x22F4), "sv_fail_2c60")
    g.load(0x22F4, "lw")
    g.branch(0x22F8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(op, ol)]}.pos_ne)")
    g.load(0x22FC, "lw")
    g.block(0x2300, 0x230A)
    ks = g.sne(0x230A, op, f"{ol}.toNat", "BitVec.ofNat 32 0x3FCC4862", "11", f"(.inl {g.slices[(op, ol)]})",
               "(.inr ⟨by decide, by decide⟩)", ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
    eq = f"memBytes M0 {op} {ol}.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4862) 11"
    g.prop_check(eq, "htst", lambda sub: tsa_ne_fail(sub, ks, 0x2312, "htst"))
    g.set_a0(ks, 0, "ite_eq_left htst")
    g.branch(0x2312, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0x2316, [2, 3, 4, 18, 19, 20, 21, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tsa2", "title": "the timestamp's SignedData",
            "doc": "From 0x21A0 to 0x2316: the token's `[0]` content is a `SignedData` sequence with nothing "
            "after it, whose version is `INTEGER 3`, whose digest algorithms are SHA-256 alone, and whose "
            "encapsulated content's type is TSTInfo.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSA2_BINDERS, "start": 0x21A0,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


TSA3_BINDERS = ("{B out bp x21 x26 sdp sdl ecp ecl : Word} "
                + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def tsa3_none(sub, k):
    """No eContent: `lbu`, `bnez` not taken, `lw`, `li s0`, `beqz` to 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, y4_{k}⟩ := R{k}")
    sub.frame_after(k, [(0x420, 0x18), (0x2E8, 8)], {0x424: ("0", f"y4_{k}")}, {0x420: ("(0 : BitVec 8)", f"y0_{k}")})
    sub.load(0x2328, "lbu")
    sub.branch(0x232C, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.load(0x2330, "lw")
    sub.block(0x2334, 0x2336)
    sub.branch(0x2336, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa3_err(sub, k):
    """A malformed eContent: `lbu`, `bnez` to 0x298E, `lbu s0`, `j` to 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
    sub.frame_after(k, [(0x420, 0x18), (0x2E8, 8)], {}, {0x420: ("(1 : BitVec 8)", f"y0_{k}")})
    sub.load(0x2328, "lbu")
    sub.branch(0x232C, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.load_any(0x298E)
    sub.jump(0x2992)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa3_oct_tail(sub):
    """`Der::octet_string` failing at 0x238C: `lw`, `sw`, `beqz` to 0x2994, `lbu s0`, `j` to 0x2C60."""
    sub.load(0x2394, "lw")
    sub.store(0x2398, "sw")
    sub.branch(0x239A, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.load_any(0x2994)
    sub.jump(0x2998)


def stage_tsa3():
    """From 0x2316 to 0x23AA: the encapsulated TSTInfo's octet string."""
    g = Gen("Tsa3")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 20: ("S", 0x1320)}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    words.update({0x2A8: "sdp", 0x2AC: "sdl", 0x2E8: "ecp", 0x2EC: "ecl"})
    params = start(g, regs, words, {("sdp", "sdl"): "sd_in", ("ecp", "ecl"): "ec_in"})
    g.block(0x2316, 0x2320)
    k, ex, rd = g.opt(0x2320, 0x420, 0x2E0, 0xA0)
    rp, rl, inp = rd
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with _ | (er{k} | {t})")
    g.sc.append(("eq", ex, f"some (.ok {t})", [t], f"hr{k}"))
    g.fork(lambda sub: tsa3_none(sub, k))
    g.fork(lambda sub: tsa3_err(sub, k))
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, y12_{k}, y16_{k}, y20_{k}, d8_{k}, d12_{k}⟩ := R{k}")
    h = f"BitVec.ofNat 32 {t}.header"
    hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
    g.frame_after(k, [(0x420, 0x18), (0x2E8, 8)],
                  {0x424: (f"({rp}) + {h}", f"y4_{k}"), 0x428: (f"BitVec.ofNat 32 {t}.len", f"y8_{k}"),
                   0x42C: (f"{rp}", f"y12_{k}"), 0x430: (hl, f"y16_{k}"),
                   0x2E8: (f"({rp}) + {hl}", f"d8_{k}"), 0x2EC: (f"({rl}) - {hl}", f"d12_{k}")},
                  {0x420: ("(0 : BitVec 8)", f"y0_{k}"), 0x434: (f"BitVec.ofNat 8 {t}.tag", f"y20_{k}")})
    g.slices[(f"({rp}) + {h}", f"BitVec.ofNat 32 {t}.len")] = f"({inp}.contentW (opt_ok_elem hr{k}))"
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW (opt_ok_elem hr{k}))"
    g.load(0x2328, "lbu")
    g.branch(0x232C, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load(0x2330, "lw")
    g.block(0x2334, 0x2336)
    g.branch(0x2336, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.ok_ne (opt_ok_elem hr{k}))")
    g.load(0x233A, "lw")
    g.load(0x233E, "lw")
    g.block(0x2342, 0x2356)
    g.store(0x2356, "sw")
    g.store(0x2358, "sb")
    g.store(0x235C, "sb")
    g.store(0x2360, "sb")
    g.block(0x2364, 0x2368)
    g.store(0x2368, "sb")
    g.store(0x236C, "sw")
    g.block(0x236E, 0x2378)
    g.store(0x2378, "sw")
    g.block(0x237A, 0x237C)
    g.assemble_word(0x158C, f"BitVec.ofNat 32 {t}.len")
    tsa_rest0(g, 0x237C, "hrest0", 0x2C60, 12)
    g.block(0x2380, 0x238C)
    k2, vp, vl = g.oct(0x238C, 0x420, 0x1588, tsa3_oct_tail, "sv_fail_2c60")
    g.load(0x2394, "lw")
    g.store(0x2398, "sw")
    g.branch(0x239A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(vp, vl)]}.pos_ne)")
    g.load(0x239E, "lw")
    tsa_rest0(g, 0x23A2, "hrest1", 0x2C60)
    g.load(0x23A6, "lw")
    stmt, proof = finish(g, 0x23AA, [2, 3, 4, 8, 9, 18, 19, 20, 21, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tsa3", "title": "the timestamp's TSTInfo",
            "doc": "From 0x2316 to 0x23AA: the encapsulated content has its `[0]` eContent with nothing after "
            "it, an octet string with nothing after it, whose address goes to frame offset 0x70 and length "
            "to `s5`.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSA3_BINDERS, "start": 0x2316,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


TSA4_BINDERS = ("{B out bp x21 x26 sdp sdl : Word} "
                + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def tsa4_err(sub, k):
    """Malformed certificates: `lbu`, `bnez` to 0x298E, `lbu s0`, `j` to 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
    sub.frame_after(k, [(0x420, 0x18), (0x2A8, 8)], {}, {0x420: ("(1 : BitVec 8)", f"y0_{k}")})
    sub.load(0x23BC, "lbu")
    sub.branch(0x23C0, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.load_any(0x298E)
    sub.jump(0x2992)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa4_crl(g):
    """From 0x23C4: the `SignedData` reader's length; when it isn't zero, the
    next tag must not be `[1]` (CRLs). Both ways reach 0x23DC."""
    g.load(0x23C4, "lw")
    rl = lean_val(g.regs[10])
    rp = lean_val(g.words[0x2A8])
    inp = g.slices[(rp, rl)]
    P = f"{rl} = 0 ∨ (M0 ({rp})).toNat ≠ 0xA1"
    g.pinned |= {"hnz", "ha1"}

    def crl(sub):
        sub.emit("  have hnz : ¬ " + f"{rl} = 0 := fun h => hcrl (.inl h)")
        sub.emit(f"  have ha1 : (M0 ({rp})).toNat = 0xA1 := Decidable.of_not_not fun h => hcrl (.inr h)")
        sub.branch(0x23C8, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f hnz")
        sub.load(0x23CA, "lw")
        sub.load_in(0x23CE, inp, "(toNat_pos_of_ne hnz)")
        sub.block(0x23D2, 0x23D6)
        sub.block(0x23D6, 0x23D8)
        sub.branch(0x23D8, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_tag_a1_t ha1")
        sub.fail(sub.fail_proof(("prop", "hcrl")), "sv_fail_2c60")
    g.prop_check(P, "hcrl", crl)
    g.emit(f"  by_cases hz : {rl} = 0")

    def zero(sub):
        sub.branch(0x23C8, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t hz")
        sub.exit_here()
    g.fork(zero)
    g.emit(f"  have ha1 : (M0 ({rp})).toNat ≠ 0xA1 := hcrl.resolve_left hz")
    g.branch(0x23C8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hz")
    g.load(0x23CA, "lw")
    g.load_in(0x23CE, inp, "(toNat_pos_of_ne hz)")
    g.block(0x23D2, 0x23D6)
    g.block(0x23D6, 0x23D8)
    g.branch(0x23D8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_tag_a1_f ha1")


def stage_tsa4(present):
    """From 0x23AA to 0x23DC: the optional certificates, and no CRLs."""
    g = Gen("Tsa4" + ("s" if present else "n"))
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 20: ("S", 0x1320)}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    words.update({0x2A8: "sdp", 0x2AC: "sdl"})
    params = start(g, regs, words, {("sdp", "sdl"): "sd_in"})
    L = "(memBytes M0 (sdp) (sdl).toNat)"
    params.append(f"(hce : derOptRes 0xA0 {L} {'≠' if present else '='} none)")
    g.block(0x23AA, 0x23B4)
    k, ex, rd = g.opt2(0x23B4, 0x420, 0x2A0, 0xA0)
    rp, rl, inp = rd
    if present:
        t = f"tl{k}"
        g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        g.emit(f"  rcases r{k} with _ | (er{k} | {t})")
        g.sc.append(("eq", ex, f"some (.ok {t})", [t], f"hr{k}"))
        g.fork(lambda sub: sub.emit(f"  exact absurd hr{k} hce"))
        g.fork(lambda sub: tsa4_err(sub, k))
        g.emit(f"  rw [hr{k}] at R{k}")
        g.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, y12_{k}, y16_{k}, y20_{k}, d8_{k}, d12_{k}⟩ := R{k}")
        h = f"BitVec.ofNat 32 {t}.header"
        hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
        g.frame_after(k, [(0x420, 0x18), (0x2A8, 8)],
                      {0x424: (f"({rp}) + {h}", f"y4_{k}"), 0x428: (f"BitVec.ofNat 32 {t}.len", f"y8_{k}"),
                       0x42C: (f"{rp}", f"y12_{k}"), 0x430: (hl, f"y16_{k}"),
                       0x2A8: (f"({rp}) + {hl}", f"d8_{k}"), 0x2AC: (f"({rl}) - {hl}", f"d12_{k}")},
                      {0x420: ("(0 : BitVec 8)", f"y0_{k}"), 0x434: (f"BitVec.ofNat 8 {t}.tag", f"y20_{k}")})
        g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW (opt_ok_elem hr{k}))"
    else:
        g.emit(f"  rw [hce] at R{k}")
        g.emit(f"  obtain ⟨y0_{k}, y4_{k}⟩ := R{k}")
        g.emit(f"  replace K{k} := N{k} hce")
        g.frame_after(k, [(0x420, 0x18)], {0x424: ("0", f"y4_{k}")}, {0x420: ("(0 : BitVec 8)", f"y0_{k}")})
    g.load(0x23BC, "lbu")
    g.branch(0x23C0, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    tsa4_crl(g)
    keep = set(g.words) - {0x424, 0x428, 0x42C, 0x430}
    stmt, proof = finish(g, 0x23DC, [2, 3, 4, 9, 18, 19, 20, 21, 26, 27], keep, set())
    info = {"name": "sv_tsa4" + ("s" if present else "n"),
            "title": "the timestamp's certificates" + ("" if present else ", absent"),
            "doc": "From 0x23AA to 0x23DC: the `SignedData`'s `[0]` certificates are "
            + ("present and well formed" if present else "absent") + ", and the next field isn't `[1]` CRLs.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSA4_BINDERS, "start": 0x23AA,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


TSA5_BINDERS = ("{B out bp x21 x26 sip sil : Word} "
                + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def tsa5_ii_fail(sub, k, err):
    """`Der::integer_is` failing at 0x245A: an error goes to 0x24A0, a different
    value to 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    sub.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x{1 if err else 0:X} := a0_{k}")
    sub.regs[10] = ("C", 1 if err else 0)
    if not err:
        sub.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x0 := by rw [a1_{k}]; rfl")
        sub.regs[11] = ("C", 0)
    sub.frame_after(k, [(0x208, 8)], {})
    sub.block(0x2462, 0x2464)
    if err:
        sub.branch(0x2464, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.block(0x24A0, 0x24A2)
        sub.jump(0x24A2)
    else:
        sub.branch(0x2464, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.block(0x2466, 0x2468)
        sub.branch(0x2468, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; decide")
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa5_sha_fail(sub, k, err):
    """`tsa::is_sha256` failing at 0x2494: an error goes through 0x24A0, another
    algorithm to 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    sub.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x{1 if err else 0:X} := a0_{k}")
    sub.regs[10] = ("C", 1 if err else 0)
    if not err:
        sub.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x0 := by rw [a1_{k}]; rfl")
        sub.regs[11] = ("C", 0)
    sub.frame_after(k, [(0x208, 8)], {})
    sub.block(0x249C, 0x249E)
    if err:
        sub.branch(0x249E, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.block(0x24A0, 0x24A2)
        sub.jump(0x24A2)
    else:
        sub.branch(0x249E, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.block(0x24AA, 0x24AC)
        sub.branch(0x24AC, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; decide")
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa5_elem_tail(sub):
    """`Der::element` failing at 0x2476: `lw`, `beqz` to 0x2994, `lbu s0`, `j` to 0x2C60."""
    sub.load(0x247E, "lw")
    sub.branch(0x2482, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.load_any(0x2994)
    sub.jump(0x2998)


def tsa5_none(sub, k):
    """No signed attributes: `lbu`, `bnez` not taken, `lw`, `beqz` to 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, y4_{k}⟩ := R{k}")
    sub.frame_after(k, [(0x420, 0x18), (0x208, 8)], {0x424: ("0", f"y4_{k}")}, {0x420: ("(0 : BitVec 8)", f"y0_{k}")})
    sub.load(0x24C2, "lbu")
    sub.branch(0x24C6, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.load(0x24CA, "lw")
    sub.branch(0x24CE, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa5_err(sub, k):
    """Malformed signed attributes: `lbu`, `bnez` to 0x298E, `lbu s0`, `j` to 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
    sub.frame_after(k, [(0x420, 0x18), (0x208, 8)], {}, {0x420: ("(1 : BitVec 8)", f"y0_{k}")})
    sub.load(0x24C2, "lbu")
    sub.branch(0x24C6, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.load_any(0x298E)
    sub.jump(0x2992)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsa5_noattrs(sub, hname):
    """An empty signed attributes set: `beqz` to 0x2682, then no digest and no
    content type, and `beqz` to 0x29A6."""
    sub.branch(0x2502, True, f"by rw [g{sub.k}_20, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not {hname})")
    sub.block(0x2682, 0x2686)
    sub.pinned.add(f"g{sub.k + 1}_11")
    sub.load(0x2686, "lw")
    sub.block(0x2688, 0x268A)
    kk = sub.k
    sub.emit(f"  have g{kk}_10 : reg n{kk} a0 = BitVec.ofNat 32 0x0 := by")
    sub.emit(f"    rw [rb{kk}]; simp +decide only [runBlock, BInstr.run, sv{sub.name}2688, upd, ↓reduceIte, aluEval]")
    sub.emit(f"    rw [g{kk - 1}_11]; exact BitVec.and_zero")
    sub.regs[10] = ("C", 0)
    sub.branch(0x268A, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.block(0x29A6, 0x29A8)
    sub.jump(0x29A8)
    sub.fail(sub.fail_proof(("prop", hname)), "sv_fail_2c60")


def stage_tsa5():
    """From 0x23DC to the signed attributes loop at 0x2506."""
    g = Gen("Tsa5")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 20: ("S", 0x1320)}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    words.update({0x2A8: "sip", 0x2AC: "sil"})
    params = start(g, regs, words, {("sip", "sil"): "si_in"}) + ["(D0 : SvData M0)"]
    g.block(0x23DC, 0x23E2)
    k1, t1, rd1 = tsa_read(g, 0x23E2, 0x2A0, "set")
    g.block(0x23F6, 0x2400)
    g.mc(0x2400, 0x17D, 0x425, 0xB)
    g.load(0x2408, "lw")
    g.store(0x240C, "sw")
    g.store(0x2410, "sb")
    g.word_of_bytes(0x17C, f"BitVec.ofNat 32 {t1}.len")
    tsa_rest0(g, 0x2414, "hrest0", 0x2838)
    g.block(0x2418, 0x241E)
    k2, t2, rd2 = tsa_read(g, 0x241E, 0x178)
    g.block(0x2432, 0x243C)
    g.mc(0x243C, 0x205, 0x425, 0xB)
    g.load(0x2444, "lw")
    g.store(0x2448, "sw")
    g.store(0x244C, "sb")
    g.word_of_bytes(0x204, f"BitVec.ofNat 32 {t2}.len")
    g.block(0x2450, 0x2452)
    tsa_rest0(g, 0x2452, "hrest1", 0x2C60)
    g.block(0x2456, 0x245A)
    k, ex, rd = g.iis(0x245A, 0x200)
    rp, rl, inp = rd
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with b{k} | (_ | _)")
    g.sc.append(("eq", ex, ".ok true", [], f"hr{k}"))
    g.fork(lambda sub: tsa5_ii_fail(sub, k, True))
    g.fork(lambda sub: tsa5_ii_fail(sub, k, False))
    g.emit(f"  obtain ⟨te{k}, hte{k}⟩ := ii_ok_elem hr{k}")
    g.sc.append(("eq", f"derElement 2 (memBytes M0 ({rp}) ({rl}).toNat)", f".ok te{k}", [f"te{k}"], f"hte{k}"))
    g.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} te{k} hte{k}")
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    g.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x0 := a0_{k}")
    g.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x1 := by rw [a1_{k}]; rfl")
    g.regs[10] = ("C", 0)
    g.regs[11] = ("C", 1)
    hl = f"BitVec.ofNat 32 (te{k}.header + te{k}.len)"
    g.frame_after(k, [(0x208, 8)], {0x208: (f"({rp}) + {hl}", f"d8_{k}"), 0x20C: (f"({rl}) - {hl}", f"d12_{k}")})
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hte{k})"
    g.block(0x2462, 0x2464)
    g.branch(0x2464, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x2466, 0x2468)
    g.branch(0x2468, False, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
    g.block(0x246C, 0x2476)
    k, ex, rd = g.elem(0x2476, 0x420, 0x200, 0x30)
    t = g.elem_split(k, ex, 0x420, 0x200, rd, tsa5_elem_tail, "sv_fail_2c60")
    g.load(0x247E, "lw")
    g.branch(0x2482, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    g.load(0x2486, "lw")
    g.store(0x248A, "sw")
    g.load(0x248C, "lw")
    g.store(0x2490, "sw")
    g.block(0x2492, 0x2494)
    k, ex, rd = g.issha(0x2494, 0x200)
    rp, rl, inp = rd
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with b{k} | (_ | _)")
    g.sc.append(("eq", ex, ".ok true", [], f"hr{k}"))
    g.fork(lambda sub: tsa5_sha_fail(sub, k, True))
    g.fork(lambda sub: tsa5_sha_fail(sub, k, False))
    g.emit(f"  obtain ⟨te{k}, hte{k}⟩ := isSha256Of_ok_elem hr{k}")
    g.sc.append(("eq", f"derElement 0x30 (memBytes M0 ({rp}) ({rl}).toNat)", f".ok te{k}", [f"te{k}"], f"hte{k}"))
    g.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} te{k} hte{k}")
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    g.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x0 := a0_{k}")
    g.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x1 := by rw [a1_{k}]; rfl")
    g.regs[10] = ("C", 0)
    g.regs[11] = ("C", 1)
    hl = f"BitVec.ofNat 32 (te{k}.header + te{k}.len)"
    g.frame_after(k, [(0x208, 8)], {0x208: (f"({rp}) + {hl}", f"d8_{k}"), 0x20C: (f"({rl}) - {hl}", f"d12_{k}")})
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hte{k})"
    g.block(0x249C, 0x249E)
    g.branch(0x249E, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x24AA, 0x24AC)
    g.branch(0x24AC, False, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
    g.block(0x24B0, 0x24BA)
    k, ex, rd = g.opt(0x24BA, 0x420, 0x200, 0xA0)
    rp, rl, inp = rd
    t = f"tl{k}"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with _ | (er{k} | {t})")
    g.sc.append(("eq", ex, f"some (.ok {t})", [t], f"hr{k}"))
    g.fork(lambda sub: tsa5_none(sub, k))
    g.fork(lambda sub: tsa5_err(sub, k))
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, y12_{k}, y16_{k}, y20_{k}, d8_{k}, d12_{k}⟩ := R{k}")
    h = f"BitVec.ofNat 32 {t}.header"
    hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
    g.frame_after(k, [(0x420, 0x18), (0x208, 8)],
                  {0x424: (f"({rp}) + {h}", f"y4_{k}"), 0x428: (f"BitVec.ofNat 32 {t}.len", f"y8_{k}"),
                   0x42C: (f"{rp}", f"y12_{k}"), 0x430: (hl, f"y16_{k}"),
                   0x208: (f"({rp}) + {hl}", f"d8_{k}"), 0x20C: (f"({rl}) - {hl}", f"d12_{k}")},
                  {0x420: ("(0 : BitVec 8)", f"y0_{k}"), 0x434: (f"BitVec.ofNat 8 {t}.tag", f"y20_{k}")})
    g.slices[(f"({rp}) + {h}", f"BitVec.ofNat 32 {t}.len")] = f"({inp}.contentW (opt_ok_elem hr{k}))"
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW (opt_ok_elem hr{k}))"
    g.load(0x24C2, "lbu")
    g.branch(0x24C6, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load(0x24CA, "lw")
    g.branch(0x24CE, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.ok_ne (opt_ok_elem hr{k}))")
    g.block(0x24D2, 0x24D4)
    g.store(0x24D4, "sw")
    g.block(0x24D6, 0x24DA)
    g.load(0x24DA, "lw")
    g.load(0x24DE, "lw")
    g.store(0x24E0, "sw")
    g.load(0x24E2, "lw")
    g.store(0x24E4, "sw")
    g.block(0x24E6, 0x24EE)
    g.store(0x24EE, "sw")
    g.block(0x24F0, 0x24F2)
    g.store(0x24F2, "sw")
    g.store(0x24F4, "sw")
    g.block(0x24F6, 0x2500)
    g.store(0x2500, "sw")
    len_ = lean_val(g.regs[20])
    g.prop_check(f"{len_} ≠ 0", "hattrs", lambda sub: tsa5_noattrs(sub, "hattrs"))
    g.branch(0x2502, False, f"by rw [g{g.k}_20, s{g.k}.zero]; exact br_beq_f hattrs")
    stmt, proof = finish(g, 0x2506, [2, 3, 4, 9, 18, 19, 20, 21, 24, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tsa5", "title": "the timestamp's SignerInfo",
            "doc": "From 0x23DC to the signed attributes loop at 0x2506: one `SignerInfo` with version `INTEGER 1`, "
            "its `sid` element, digest algorithm SHA-256, and nonempty `[0]` signed attributes.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSA5_BINDERS, "start": 0x23DC,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


ATTR_BINDERS = ("{B out bp x21 x26 dg p0 L0 cp rem : Word} "
                + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def attr_start(g, extra_words=None):
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 9: ("S", 0x1320),
            20: ("U", "rem"), 24: ("U", "dg")}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    words.update({0x1320: "p0", 0x1324: "L0", 0x1328: "cp", 0x132C: "rem"})
    words.update(extra_words or {})
    return start(g, regs, words, {("cp", "rem"): "cr_in", ("p0", "L0"): "p0_in"})


def attr_oid_tail(sub):
    """`Der::oid` failing at 0x2552: `lw s7`, `beqz` to 0x2994, `lbu s0`, `j` to 0x2C60."""
    sub.load(0x255A, "lw")
    sub.branch(0x255E, True, f"by rw [g{sub.k}_23, s{sub.k}.zero]; rfl")
    sub.load_any(0x2994)
    sub.jump(0x2998)


def attr_lo_fail(sub, k, err):
    """`der::lists_oid` failing: an error, or the OID listed before."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    sub.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x{1 if err else 0:X} := a0_{k}")
    sub.regs[10] = ("C", 1 if err else 0)
    if not err:
        sub.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x1 := by rw [a1_{k}]; rfl")
        sub.regs[11] = ("C", 1)
    sub.block(0x25C8, 0x25CC)
    if err:
        sub.branch(0x25CC, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    else:
        sub.branch(0x25CC, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.block(0x25D0, 0x25D6)
        sub.branch(0x25D6, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def stage_tsaa():
    """One signed attribute, from the loop head at 0x2506 to 0x25DA."""
    g = Gen("Tsaa")
    params = attr_start(g)
    g.load(0x2506, "lw")

    def big(sub):
        sub.branch(0x250A, True, f"by rw [g{sub.k}_25, g{sub.k}_20]; exact br_bltu_t (by omega)")
        sub.block(0x26FA, 0x26FC)
        sub.jump(0x26FC)
        sub.fail(sub.fail_proof(("prop", "hle")), "sv_fail_2c60")
    g.prop_check("(rem).toNat ≤ (L0).toNat", "hle", big)
    g.branch(0x250A, False, f"by rw [g{g.k}_25, g{g.k}_20]; exact br_bltu_f (by omega)")
    g.load(0x250E, "lw")
    g.store(0x2510, "sw")
    g.block(0x2512, 0x251E)
    k1, t1, rd1 = tsa_read(g, 0x251E, 0x1320)
    g.block(0x2532, 0x253C)
    g.mc(0x253C, 0x325, 0x425, 0xB)
    g.store(0x2544, "sw")
    g.store(0x2548, "sb")
    g.word_of_bytes(0x324, f"BitVec.ofNat 32 {t1}.len")
    g.block(0x254C, 0x2552)
    k, op, ol = g.oid(0x2552, 0x420, 0x320, attr_oid_tail, "sv_fail_2c60")
    oid_in = g.slices[(op, ol)]
    g.load(0x255A, "lw")
    g.branch(0x255E, False, f"by rw [g{g.k}_23, s{g.k}.zero]; exact br_beq_f ({oid_in}.pos_ne)")
    g.load(0x2562, "lw")
    g.block(0x2566, 0x256C)
    k2, t2, rd2 = tsa_read(g, 0x256C, 0x320, "set")
    g.block(0x2580, 0x258E)
    g.mc(0x258E, 0x1385, 0x425, 0xB)
    g.load(0x2596, "lw")
    g.block(0x259A, 0x25A2)
    g.store(0x25A2, "sw")
    g.block(0x25A4, 0x25AE)
    g.store(0x25AE, "sb")
    g.word_of_bytes(0x1384, f"BitVec.ofNat 32 {t2}.len")
    tsa_rest0(g, 0x25B2, "hrest0", 0x2838)
    g.block(0x25B6, 0x25BA)
    g.load(0x25BA, "lw")
    g.block(0x25BC, 0x25C0)
    nl = f"((L0) - (rem)).toNat"
    k = g.lo(0x25C0, "p0", nl, op, f"{ol}.toNat", f"(p0_in.shrink (sub_le_toNat hle))", f"{oid_in}",
             ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
    ex = f"listsOidOf M0 p0 {nl} (memBytes M0 {op} {ol}.toNat)"
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with b{k} | (_ | _)")
    g.sc.append(("eq", ex, ".ok false", [], f"hr{k}"))
    g.fork(lambda sub: attr_lo_fail(sub, k, True))
    g.emit("  rotate_left")
    g.fork(lambda sub: attr_lo_fail(sub, k, False))
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    g.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x0 := a0_{k}")
    g.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x0 := by rw [a1_{k}]; rfl")
    g.regs[10] = ("C", 0)
    g.regs[11] = ("C", 0)
    g.block(0x25C8, 0x25CC)
    g.branch(0x25CC, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x25D0, 0x25D6)
    g.branch(0x25D6, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0x25DA, [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tsaa", "title": "a signed attribute's type",
            "doc": "One signed attribute, from the loop head at 0x2506 to 0x25DA: a sequence of an OID and a set "
            "with nothing after it, whose OID no earlier attribute has.",
            "params": params, "stmt": stmt, "proof": proof, "binders": ATTR_BINDERS, "start": 0x2506,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


ATTRV_BINDERS = ("{B out bp x21 x26 dg p0 L0 cp rem op ol vcp vcl : Word} "
                 + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")
CT_OID = "memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC486E) 9"
MD_OID = "memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4877) 9"


def attrv_oid_tail(sub):
    """`Der::oid` failing at 0x25FE: `lw`, `beqz` to 0x2994, `lbu s0`, `j` to 0x2C60."""
    sub.load(0x2606, "lw")
    sub.branch(0x260A, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.load_any(0x2994)
    sub.jump(0x2998)


def attrv_oct_tail(sub):
    """`Der::octet_string` failing at 0x2658: `lw`, `beqz` to 0x2994, `lbu s0`, `j` to 0x2C60."""
    sub.load(0x2660, "lw")
    sub.branch(0x2664, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.load_any(0x2994)
    sub.jump(0x2998)


def attrv_len_fail(sub):
    sub.branch(0x2670, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_m32_t h32")
    sub.fail(sub.fail_proof(("prop", "h32")), "sv_fail_2c60")


def stage_tsav(kind):
    """One signed attribute from 0x25DA to 0x267A: a contentType, a messageDigest,
    or another attribute."""
    g = Gen("Tsav" + kind)
    params = attr_start(g, {0x74: "p0", 0x1388: "vcp", 0x138C: "vcl"})
    g.regs.update({22: ("U", "ol"), 23: ("U", "op"), 25: ("U", "L0")})
    params += ["(g0_22 : reg n0 (22 : Fin 32) = ol)", "(g0_23 : reg n0 (23 : Fin 32) = op)",
               "(g0_25 : reg n0 (25 : Fin 32) = L0)", "(oid_in : SvIn B op ol.toNat)", "(vc_in : SvIn B vcp vcl.toNat)"]
    g.slices[("vcp", "vcl")] = "vc_in"
    g.slices[("op", "ol")] = "oid_in"
    if kind == "ct":
        params.append(f"(hct : {CT_OID})")
    else:
        params.append(f"(hct : ¬ {CT_OID})")
        params.append(f"(hmd : {'' if kind == 'md' else '¬ '}{MD_OID})")
    g.block(0x25DA, 0x25E8)
    ke = g.seqeq(0x25E8, "op", "ol.toNat", "BitVec.ofNat 32 0x3FCC486E", "9", "(.inl oid_in)",
                 "(.inr ⟨by decide, by decide⟩)", ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
    if kind == "ct":
        g.set_a0(ke, 1, "ite_eq_left hct")
        g.branch(0x25F0, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        g.block(0x25F2, 0x25FE)
        k, op2, ol2 = g.oid(0x25FE, 0x420, 0x1380, attrv_oid_tail, "sv_fail_2c60")
        g.load(0x2606, "lw")
        g.branch(0x260A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(op2, ol2)]}.pos_ne)")
        g.load(0x260E, "lw")
        g.block(0x2612, 0x261C)
        ks = g.sne(0x261C, op2, f"{ol2}.toNat", "BitVec.ofNat 32 0x3FCC4862", "11", f"(.inl {g.slices[(op2, ol2)]})",
                   "(.inr ⟨by decide, by decide⟩)", ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
        eq = f"memBytes M0 {op2} {ol2}.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4862) 11"

        def ne(sub):
            sub.set_a0(ks, 1, "ite_eq_right htst")
            sub.branch(0x2624, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
            sub.fail(sub.fail_proof(("prop", "htst")), "sv_fail_2c60")
        g.prop_check(eq, "htst", ne)
        g.set_a0(ks, 0, "ite_eq_left htst")
        g.branch(0x2624, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        g.load(0x2628, "lw")
        tsa_rest0(g, 0x262A, "hrest0", 0x2C60)
        g.block(0x262E, 0x2630)
        g.store(0x2630, "sw")
        g.jump(0x2632)
    else:
        g.set_a0(ke, 0, "ite_eq_right hct")
        g.branch(0x25F0, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        g.block(0x2634, 0x2642)
        km = g.seqeq(0x2642, "op", "ol.toNat", "BitVec.ofNat 32 0x3FCC4877", "9", "(.inl oid_in)",
                     "(.inr ⟨by decide, by decide⟩)", ha1=f"(by rw [g{g.k}_11, ofNat_toNat_self])")
        if kind == "md":
            g.set_a0(km, 1, "ite_eq_left hmd")
            g.branch(0x264A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            g.block(0x264C, 0x2658)
            k, vp, vl = g.oct(0x2658, 0x420, 0x1380, attrv_oct_tail, "sv_fail_2c60")
            g.load(0x2660, "lw")
            g.branch(0x2664, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(vp, vl)]}.pos_ne)")
            g.block(0x2668, 0x266A)
            g.load(0x266A, "lw")
            g.block(0x266E, 0x2670)
            g.prop_check(f"{vl} = 32", "h32", attrv_len_fail)
            g.branch(0x2670, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_m32_f h32")
            g.load(0x2674, "lw")
            tsa_rest0(g, 0x2676, "hrest0", 0x2C60)
        else:
            g.set_a0(km, 0, "ite_eq_right hmd")
            g.branch(0x264A, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    keep = set(g.words) - {0x420, 0x424, 0x428, 0x42C, 0x430}
    stmt, proof = finish(g, 0x267A, [2, 3, 4, 9, 18, 19, 20, 21, 24, 25, 26, 27], keep, set())
    titles = {"ct": "a contentType attribute", "md": "a messageDigest attribute", "other": "another signed attribute"}
    docs = {"ct": "the attribute is contentType, whose value is the TSTInfo OID with nothing after it; frame "
                  "offset 0x78 becomes 1.",
            "md": "the attribute is messageDigest, whose value is a 32-byte octet string with nothing after it; "
                  "its address goes to `s8`.",
            "other": "the attribute is neither contentType nor messageDigest, and is skipped."}
    info = {"name": "sv_tsav" + kind, "title": titles[kind],
            "doc": "From 0x25DA to 0x267A: " + docs[kind],
            "params": params, "stmt": stmt, "proof": proof, "binders": ATTRV_BINDERS, "start": 0x25DA,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


TSAL_BINDERS = ("{B out bp x21 x26 dg p0 L0 cp rem sip sil flag : Word} "
                + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS if e != 0x78) + " : Word} {v : Nat → Word} {n0 : Machine}")


def tsal_start(g):
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 9: ("S", 0x1320), 24: ("U", "dg")}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    words.update({0x78: "flag", 0x1320: "p0", 0x1324: "L0", 0x1328: "cp", 0x132C: "rem", 0x208: "sip", 0x20C: "sil"})
    return start(g, regs, words, {("cp", "rem"): "cr_in", ("p0", "L0"): "p0_in", ("sip", "sil"): "si_in"})


def stage_tsal():
    """The signed attributes loop's branch at 0x267A, with attributes left."""
    g = Gen("Tsal")
    params = tsal_start(g) + ["(hrem : rem ≠ 0)"]
    g.load(0x267A, "lw")
    g.branch(0x267E, True, f"by rw [g{g.k}_20, s{g.k}.zero]; exact br_bne_t hrem")
    stmt, proof = finish(g, 0x2506, [2, 3, 4, 9, 18, 19, 20, 21, 24, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tsal", "title": "the next signed attribute",
            "doc": "The signed attributes loop's branch at 0x267A, with attributes left: back to the loop head.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSAL_BINDERS, "start": 0x267A,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


def tsax_alg_err(sub, k):
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
    sub.frame_after(k, [(0x420, 0x1C), (0x208, 8)], {0x420: ("0", f"y0_{k}")})
    sub.load(0x269C, "lw")
    sub.branch(0x26A0, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
    sub.load_any(0x2994)
    sub.jump(0x2998)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tsax_alg_tail(g, k, inp, s4, eq_ok):
    """From 0x269C after a read with an OID: the OID against ecdsa-with-SHA384
    and no parameters. `s4` is the parameters' address: "0" or an expression;
    `eq_ok` closes the parameters test when they're absent."""
    g.load(0x269C, "lw")
    g.branch(0x26A0, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.algOid hr{k}).pos_ne")
    g.load(0x26A4, "lw")
    g.load(0x26A8, "lw")
    g.block(0x26AC, 0x26B6)
    ks = g.sne(0x26B6, f"op{k}", f"ol{k}", "BitVec.ofNat 32 0x3FCC4818", "8", f"(.inl ({inp}.algOid hr{k}))",
               "(.inr ⟨by decide, by decide⟩)")
    return ks


def stage_tsax():
    """The signed attributes loop's exit at 0x267A to 0x2704: a digest and a
    content type seen, the signature algorithm, and the signature."""
    g = Gen("Tsax")
    params = tsal_start(g) + ["(hrem : rem = 0)", "(hflag : flag = 0 ∨ flag = 1)"]
    g.load(0x267A, "lw")
    g.branch(0x267E, False, f"by rw [g{g.k}_20, s{g.k}.zero]; exact br_bne_f hrem")
    g.block(0x2682, 0x2686, {10: ("aluEval .sltu 0 (dg)",
                                  "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, svTsax2682, upd, ↓reduceIte]; rw [g{p}_24, s{p}.zero]")})
    g.load(0x2686, "lw")
    g.block(0x2688, 0x268A)

    def nodigest(sub):
        sub.branch(0x268A, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t ((snez_and_eq hflag).mpr hfl)")
        sub.block(0x29A6, 0x29A8)
        sub.jump(0x29A8)
        sub.fail(sub.fail_proof(("prop", "hfl")), "sv_fail_2c60")
    g.prop_check("dg ≠ 0 ∧ flag = 1", "hfl", nodigest)
    g.branch(0x268A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f fun e => (snez_and_eq hflag).mp e hfl")
    g.block(0x268E, 0x2694)
    k, ex, rd = g.alg_w(0x2694, 0x420, 0x200)
    rp, rl, inp = rd
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with ab{k} | ⟨⟨op{k}, ol{k}⟩, _ | ⟨prp{k}, pu{k}⟩⟩")
    g.sc.append(("eq", ex, f".ok ((op{k}, ol{k}), none)", [f"op{k}", f"ol{k}"], f"hr{k}"))
    g.fork(lambda sub: tsax_alg_err(sub, k))
    g.emit("  rotate_left")

    def params_(sub):
        sub.emit(f"  rw [hr{k}] at R{k}")
        sub.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, -, -⟩ := R{k}")
        sub.frame_after(k, [(0x420, 0x1C), (0x208, 8)],
                        {0x420: (f"op{k}", f"y0_{k}"), 0x424: (f"BitVec.ofNat 32 ol{k}", f"y4_{k}"),
                         0x428: (f"prp{k} + BitVec.ofNat 32 pu{k}.header", f"y8_{k}")})
        ks = tsax_alg_tail(sub, k, inp, None, None)
        eq = f"memBytes M0 op{k} ol{k} = memBytes M0 (BitVec.ofNat 32 0x3FCC4818) 8"
        sub.emit(f"  by_cases hoq : {eq}")

        def same(sub2):
            sub2.set_a0(ks, 0, "ite_eq_left hoq")
            sub2.block(0x26BE, 0x26C0)
            sub2.branch(0x26C0, False, f"by rw [g{sub2.k}_10, s{sub2.k}.zero]; decide")
            sub2.branch(0x26C4, True, f"by rw [g{sub2.k}_20, s{sub2.k}.zero]; exact br_bne_t ({inp}.algParams hr{k})")
            sub2.fail(sub2.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")
        sub.fork(same)
        sub.set_a0(ks, 1, "ite_eq_right hoq")
        sub.block(0x26BE, 0x26C0)
        sub.branch(0x26C0, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")
    g.fork(params_)
    g.emit(f"  obtain ⟨te{k}, hte{k}⟩ := alg_ok_elem hr{k}")
    g.sc.append(("eq", f"derElement 0x30 (memBytes M0 ({rp}) ({rl}).toNat)", f".ok te{k}", [f"te{k}"], f"hte{k}"))
    g.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} te{k} hte{k}")
    g.emit(f"  rw [ofNat_toNat_self] at d12_{k}")
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}⟩ := R{k}")
    hl = f"BitVec.ofNat 32 (te{k}.header + te{k}.len)"
    nrl = rl
    g.frame_after(k, [(0x420, 0x1C), (0x208, 8)],
                  {0x420: (f"op{k}", f"y0_{k}"), 0x424: (f"BitVec.ofNat 32 ol{k}", f"y4_{k}"), 0x428: ("0", f"y8_{k}"),
                   0x208: (f"({rp}) + {hl}", f"d8_{k}"), 0x20C: (f"({nrl}) - {hl}", f"d12_{k}")})
    g.slices[(f"({rp}) + {hl}", f"({nrl}) - {hl}")] = f"({inp}.restW hte{k})"
    ks = tsax_alg_tail(g, k, inp, "0", None)
    eq = f"memBytes M0 op{k} ol{k} = memBytes M0 (BitVec.ofNat 32 0x3FCC4818) 8"

    def ne(sub):
        sub.set_a0(ks, 1, "ite_eq_right hoid")
        sub.block(0x26BE, 0x26C0)
        sub.branch(0x26C0, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", "hoid")), "sv_fail_2c60")
    g.prop_check(eq, "hoid", ne)
    g.set_a0(ks, 0, "ite_eq_left hoid")
    g.block(0x26BE, 0x26C0)
    g.branch(0x26C0, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.branch(0x26C4, False, f"by rw [g{g.k}_20, s{g.k}.zero]; rfl")
    g.block(0x26C8, 0x26D2)

    def oct_tail(sub):
        sub.load(0x26DA, "lw")
        sub.branch(0x26DC, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; rfl")
        sub.load_any(0x26FE)
        sub.jump(0x2702)
    k, vp, vl = g.oct(0x26D2, 0x1380, 0x200, oct_tail, "sv_fail_2c60")
    g.load(0x26DA, "lw")
    g.branch(0x26DC, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_beq_f ({g.slices[(vp, vl)]}.pos_ne)")
    g.load(0x26DE, "lw")
    g.block(0x26E0, 0x26E4)
    g.es2(0x26E4, 0x420, vp, f"({vl}).toNat", g.slices[(vp, vl)], f"(by rw [g{g.k}_12, ofNat_toNat_self])")
    stmt, proof = finish(g, 0x2704, [2, 3, 4, 8, 9, 18, 19, 21, 24, 25, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tsax", "title": "the timestamp's signature algorithm",
            "doc": "The signed attributes loop's exit at 0x267A to 0x2704: both a message digest and a content type "
            "were seen, the `SignerInfo`'s signature algorithm is ecdsa-with-SHA384 with no parameters, and its "
            "signature is a DER ECDSA signature with 48-byte scalars.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSAL_BINDERS, "start": 0x267A,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


TST_BINDERS = ("{B out bp x21 x26 dg sip sil : Word} {sr ss : Bytes} "
               + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def tst1_oct_tail(sub):
    sub.load(0x2820, "lw")
    sub.branch(0x2824, True, f"by rw [g{sub.k}_22, s{sub.k}.zero]; rfl")
    sub.load_any(0x2994)
    sub.jump(0x2998)


def tst_len_fail(sub):
    sub.branch(0x282E, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_m32_t h32")
    sub.fail(sub.fail_proof(("prop", "h32")), "sv_fail_2c60")


def stage_tst1():
    """From 0x2704 to 0x283C: the TSTInfo sequence, its version, policy, and
    message imprint."""
    g = Gen("Tst1")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            25: ("U", "(BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32", "BitVec.ofNat 8 (sr.getD 0 0)")}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    words.update({0x208: "sip", 0x20C: "sil"})
    params = start(g, regs, words, {("w70", "x21"): "tst_in"}) + ["(D0 : SvData M0)"]
    g.ranges[0x421] = (48, "BitVec.ofNat 8 (sr.getD j 0)")
    g.ranges[0x451] = (48, "BitVec.ofNat 8 (ss.getD j 0)")
    params += ["(q0_421 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (sr.getD j 0))",
               "(q0_451 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 (ss.getD j 0))"]
    g.block(0x2704, 0x2714)
    g.mc(0x2714, 0x1020, 0x422, 0x5F)
    g.load(0x271C, "lw")
    tsa_rest0(g, 0x2720, "hsi0", 0x2C60)
    g.load(0x2724, "lw")
    g.block(0x2726, 0x2728)
    g.store(0x2728, "sw")
    g.block(0x272A, 0x272C)
    for o in (0x272C, 0x272E, 0x2730):
        g.store(o, "sw")
    g.block(0x2732, 0x2738)
    k1, t1, rd1 = tsa_read(g, 0x2738, 0x240)
    g.block(0x274C, 0x275A)
    g.mc(0x275A, 0x1325, 0x425, 0xB)
    g.load(0x2762, "lw")
    g.block(0x2766, 0x276E)
    g.store(0x276E, "sw")
    g.block(0x2770, 0x277A)
    g.store(0x277A, "sb")
    g.word_of_bytes(0x1324, f"BitVec.ofNat 32 {t1}.len")
    tsa_rest0(g, 0x277E, "hrest0", 0x2838)
    g.block(0x2780, 0x278A)
    tsa_iis(g, 0x278A, 0x1320, 0x2792, 0x29A6)
    g.block(0x27A0, 0x27AC)
    k, op, ol = g.oid(0x27AC, 0x420, 0x1320, lambda sub: tsa_oid_tail(sub, 0x27B4), "sv_fail_2c60")
    g.load(0x27B4, "lw")
    g.branch(0x27B8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({g.slices[(op, ol)]}.pos_ne)")
    g.block(0x27BC, 0x27C8)
    k2, t2, rd2 = tsa_read(g, 0x27C8, 0x1320)
    g.block(0x27DC, 0x27E6)
    g.mc(0x27E6, 0x325, 0x425, 0xB)
    g.store(0x27EE, "sw")
    g.store(0x27F2, "sb")
    g.word_of_bytes(0x324, f"BitVec.ofNat 32 {t2}.len")
    g.block(0x27F6, 0x27F8)
    k, ex, rd = g.issha(0x27F8, 0x320)
    rp, rl, inp = rd
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with b{k} | (_ | _)")
    g.sc.append(("eq", ex, ".ok true", [], f"hr{k}"))
    g.fork(lambda sub: tsa_issha_fail(sub, k, 0x320, True, 0x2800))
    g.fork(lambda sub: tsa_issha_fail(sub, k, 0x320, False, 0x2800))
    g.emit(f"  obtain ⟨te{k}, hte{k}⟩ := isSha256Of_ok_elem hr{k}")
    g.sc.append(("eq", f"derElement 0x30 (memBytes M0 ({rp}) ({rl}).toNat)", f".ok te{k}", [f"te{k}"], f"hte{k}"))
    g.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} te{k} hte{k}")
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  obtain ⟨a0_{k}, a1_{k}⟩ := R{k}")
    g.emit(f"  have g{k}_10 : reg n{k} a0 = BitVec.ofNat 32 0x0 := a0_{k}")
    g.emit(f"  have g{k}_11 : reg n{k} a1 = BitVec.ofNat 32 0x1 := by rw [a1_{k}]; rfl")
    g.regs[10] = ("C", 0)
    g.regs[11] = ("C", 1)
    hl = f"BitVec.ofNat 32 (te{k}.header + te{k}.len)"
    g.frame_after(k, [(0x328, 8)], {0x328: (f"({rp}) + {hl}", f"d8_{k}"), 0x32C: (f"({rl}) - {hl}", f"d12_{k}")})
    g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hte{k})"
    tsa_ii_tests(g, 0x2800, None, None)
    g.block(0x2812, 0x2818)
    k, vp, vl = g.oct(0x2818, 0x420, 0x320, tst1_oct_tail, "sv_fail_2c60")
    g.load(0x2820, "lw")
    g.branch(0x2824, False, f"by rw [g{g.k}_22, s{g.k}.zero]; exact br_beq_f ({g.slices[(vp, vl)]}.pos_ne)")
    g.load(0x2828, "lw")
    g.block(0x282C, 0x282E)
    g.prop_check(f"{vl} = 32", "h32", tst_len_fail)
    g.branch(0x282E, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_m32_f h32")
    g.load(0x2832, "lw")
    rem = lean_val(g.regs[10])

    def rest_fail(sub):
        sub.branch(0x2836, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f hrest1")
        sub.block(0x2838, 0x283A)
        sub.jump(0x283A)
        sub.fail(sub.fail_proof(("prop", "hrest1")), "sv_fail_2c60")
    g.prop_check(f"{rem} = 0", "hrest1", rest_fail)
    g.branch(0x2836, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hrest1")
    stmt, proof = finish(g, 0x283C, [2, 3, 4, 8, 18, 19, 20, 21, 22, 24, 25, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tst1", "title": "the TSTInfo's version, policy, and message imprint",
            "doc": "From 0x2704 to 0x283C: nothing follows the `SignerInfo`'s signature, the encapsulated content "
            "is one `TSTInfo` sequence whose version is `INTEGER 1`, whose policy is an OID, and whose message "
            "imprint is a SHA-256 algorithm identifier and a 32-byte digest with nothing after them.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TST_BINDERS, "start": 0x2704,
            "import": "C3BootProofs.Proofs.SvTsa"}
    return g, info


TST_WORDS = sorted(DPV_WORDS + [0x78])
TST2_BINDERS = ("{B out bp x21 x26 dg dp rp rl : Word} {sr ss : Bytes} "
                + "{" + " ".join(f"w{e:x}" for e in TST_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def tst_start(g):
    """The state after the message imprint: the TSTInfo's reader at 0x1320
    holds (`rp`, `rl`), and the signature's bytes are at 0x1020."""
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            25: ("U", "(BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32", "BitVec.ofNat 8 (sr.getD 0 0)"),
            8: ("C", 0x18), 20: ("S", 0x1320), 22: ("U", "dp")}
    words = {e: f"w{e:x}" for e in TST_WORDS}
    words.update({0x1328: "rp", 0x132C: "rl"})
    params = start(g, regs, words, {("rp", "rl"): "rd_in"}) + ["(D0 : SvData M0)"]
    g.ranges[0x1020] = (47, "BitVec.ofNat 8 (sr.getD (1 + j) 0)")
    g.ranges[0x104F] = (48, "BitVec.ofNat 8 (ss.getD j 0)")
    params += ["(q0_1020 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))",
               "(q0_104f : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0))"]
    return params


TST_KEEP = [2, 3, 4, 8, 18, 19, 20, 21, 22, 24, 25, 26, 27]


def stage_tst2():
    """From 0x283C to 0x28BC: the serial number and the generation time."""
    g = Gen("Tst2")
    params = tst_start(g)
    g.block(0x283C, 0x2848)
    g.pinned |= {f"ipin{g.k + 1}", f"ilpos{g.k + 1}"}
    k, rd = g.pos(0x2848, 0x420, 0x1320, lambda sub: tsa_oid_tail(sub, 0x2850), "sv_fail_2c60")
    inp = rd[2]
    g.emit(f"  obtain ⟨ipin{k}, ilpos{k}⟩ := {inp}.posIntIn hr{k} hr{k}b")
    g.load(0x2850, "lw")
    g.branch(0x2854, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.serial_ne hr{k} hr{k}b)")
    g.load(0x2858, "lw")
    g.branch(0x285C, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_beq_f fun e => by rw [e] at ilpos{k}; exact absurd ilpos{k} (by decide)")
    g.load_in(0x285E, f"ipin{k}", f"ilpos{k}")
    b0 = lean_val(g.regs[10])
    g.block(0x2862, 0x2866, {10: (f"aluEval .sltu ({b0}) 1",
                                  "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, svTst22862, upd, ↓reduceIte]; rw [g{p}_10]")})
    a0v = lean_val(g.regs[10])
    a1v = lean_val(g.regs[11])
    g.block(0x2866, 0x2868, {11: (f"({a1v}) - ({a0v})",
                                  "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, svTst22866, upd, ↓reduceIte]; rw [g{p}_11, g{p}_10]; rfl")})
    g.block(0x2868, 0x286A)
    hz = "hser"
    big = lean_val(g.regs[11])

    def fail_long(sub):
        sub.branch(0x286A, True, f"by rw [g{sub.k}_10, g{sub.k}_11]; exact br_bltu_t (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega)")
        sub.fail(sub.fail_proof(("prop", hz)), "sv_fail_2c60")
    g.prop_check(f"({big}).toNat ≤ 20", hz, fail_long)
    g.branch(0x286A, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bltu_f (by rw [show (BitVec.ofNat 32 0x14).toNat = 20 from rfl]; omega)")
    g.block(0x286E, 0x287C)
    k, ex, rd = g.elem(0x287C, 0x420, 0x1320, 0x18)
    def gt_elem_tail(sub):
        sub.load(0x2884, "lw")
        sub.branch(0x2888, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; rfl")
        sub.load_any(0x2994)
        sub.jump(0x2998)
    t = g.elem_split(k, ex, 0x420, 0x1320, rd, gt_elem_tail, "sv_fail_2c60")
    g.load(0x2884, "lw")
    g.branch(0x2888, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_beq_f ({rd[2]}.ok_ne hr{k})")
    g.load(0x288C, "lw")
    g.block(0x2890, 0x2898)
    cp = f"({rd[0]}) + BitVec.ofNat 32 {t}.header"
    cl = f"BitVec.ofNat 32 {t}.len"
    g.gt(0x2898, 0x1380, cp, f"({cl}).toNat", g.slices[(cp, cl)], f"(by rw [g{g.k}_12, ofNat_toNat_self])")
    g.load(0x28A0, "lbu")
    g.branch(0x28A4, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x28AC, 0x28B4)
    g.load(0x28B4, "lw")
    g.store(0x28B6, "sw")
    g.load(0x28B8, "lw")
    g.store(0x28BA, "sw")
    stmt, proof = finish(g, 0x28BC, TST_KEEP, set(g.words), set(g.bytes))
    info = {"name": "sv_tst2", "title": "the TSTInfo's serial number and time",
            "doc": "From 0x283C to 0x28BC: the TSTInfo's serial number is a positive integer of at most 20 "
            "bytes, not counting a leading zero, and its `genTime` is a `GeneralizedTime`, whose seconds "
            "go to the words at offsets 0x3C and 0x78.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TST2_BINDERS, "start": 0x283C,
            "import": "C3BootProofs.Proofs.SvGt"}
    return g, info


def tst_opt_err(sub, k, dc, lbu_off, inverted):
    """A malformed optional field: `lbu`, then the error byte at 0x421 and 0x2C60."""
    sub.emit(f"  rw [hr{k}] at R{k}")
    sub.emit(f"  obtain ⟨y0_{k}, -⟩ := R{k}")
    sub.frame_after(k, [(0x420, 0x18), (dc + 8, 8)], {}, {0x420: ("(1 : BitVec 8)", f"y0_{k}")})
    sub.load(lbu_off, "lbu")
    sub.branch(lbu_off + 4, not inverted, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
    sub.load_any(0x298E)
    sub.jump(0x2992)
    sub.fail(sub.fail_proof(("eq", f"hr{k}")), "sv_fail_2c60")


def tst_opt(g, off, dc, tag, present, lbu_off, inverted=False):
    """`Der::optional` at `off` on the reader at `dc`, whose field is present
    or not as the stage's `hce` says; then `lbu` of the error flag at `lbu_off`
    and its branch, which `inverted` says is a `beqz` to continue rather than a
    `bnez` to fail."""
    k, ex, rd = g.opt2(off, 0x420, dc, tag)
    rp, rl, inp = rd
    if present:
        t = f"tl{k}"
        g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
        g.emit(f"  rcases r{k} with _ | (er{k} | {t})")
        g.sc.append(("eq", ex, f"some (.ok {t})", [t], f"hr{k}"))
        g.fork(lambda sub: sub.emit(f"  exact absurd hr{k} hce"))
        g.fork(lambda sub: tst_opt_err(sub, k, dc, lbu_off, inverted))
        g.emit(f"  rw [hr{k}] at R{k}")
        g.emit(f"  obtain ⟨y0_{k}, y4_{k}, y8_{k}, y12_{k}, y16_{k}, y20_{k}, d8_{k}, d12_{k}⟩ := R{k}")
        h = f"BitVec.ofNat 32 {t}.header"
        hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
        g.frame_after(k, [(0x420, 0x18), (dc + 8, 8)],
                      {0x424: (f"({rp}) + {h}", f"y4_{k}"), 0x428: (f"BitVec.ofNat 32 {t}.len", f"y8_{k}"),
                       0x42C: (f"{rp}", f"y12_{k}"), 0x430: (hl, f"y16_{k}"),
                       dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")},
                      {0x420: ("(0 : BitVec 8)", f"y0_{k}"), 0x434: (f"BitVec.ofNat 8 {t}.tag", f"y20_{k}")})
        g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW (opt_ok_elem hr{k}))"
    else:
        g.emit(f"  rw [hce] at R{k}")
        g.emit(f"  obtain ⟨y0_{k}, y4_{k}⟩ := R{k}")
        g.emit(f"  replace K{k} := N{k} hce")
        g.frame_after(k, [(0x420, 0x18)], {0x424: ("0", f"y4_{k}")}, {0x420: ("(0 : BitVec 8)", f"y0_{k}")})
    g.load(lbu_off, "lbu")
    g.branch(lbu_off + 4, inverted, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    return k


def tst_opt_info(name, start_, end, present, title, doc):
    return {"name": name, "title": title + ("" if present else ", absent"), "doc": doc,
            "binders": TST2_BINDERS, "start": start_, "import": "C3BootProofs.Proofs.SvGt"}


def stage_tst3(present):
    """From 0x28BC to 0x28DA: the optional accuracy."""
    g = Gen("Tst3" + ("s" if present else "n"))
    params = tst_start(g)
    params.append(f"(hce : derOptRes 0x30 (memBytes M0 (rp) (rl).toNat) {'≠' if present else '='} none)")
    g.block(0x28BC, 0x28CC)
    tst_opt(g, 0x28CC, 0x1320, 0x30, present, 0x28D4)
    keep = set(g.words) - {0x424, 0x428, 0x42C, 0x430}
    stmt, proof = finish(g, 0x28DA, TST_KEEP, keep, set())
    info = tst_opt_info("sv_tst3" + ("s" if present else "n"), 0x28BC, 0x28DA, present, "the TSTInfo's accuracy",
                        "From 0x28BC to 0x28DA: the TSTInfo's optional `accuracy` sequence is "
                        + ("present and well formed." if present else "absent."))
    info.update({"params": params, "stmt": stmt, "proof": proof})
    return g, info


TST4_DOC = {
    "e0": ("0x28DA", 0x2952, "the TSTInfo ends after its accuracy", "nothing follows the accuracy."),
    "o": ("0x28DA", 0x2918, "the TSTInfo's ordering", "the next field is a `BOOLEAN` `ordering`, which is TRUE."),
    "x0": ("0x28DA", 0x2932, "the TSTInfo's next field", "the next field isn't a `BOOLEAN`; its tag goes to `a0`."),
    "e1": ("0x2918", 0x2952, "the TSTInfo ends after its ordering", "nothing follows the ordering."),
    "x1": ("0x2918", 0x2932, "the TSTInfo's field after ordering", "a field follows the ordering; its tag goes to `a0`."),
    "nn": ("0x2932", 0x2952, "no nonce", "the next field isn't an `INTEGER` nonce."),
    "ns": ("0x2932", 0x2952, "the TSTInfo's nonce", "the next field is an `INTEGER` nonce."),
}


def tst4_peek(g, at):
    """`lw` of the reader's length, `beqz`, then `lw` and `lbu` of the next tag:
    from 0x28DA (`at` = 0x28E2) or 0x2918 (`at` = 0x2920)."""
    g.block(at - 8, at)
    g.load(at, "lw")


def stage_tst4(kind):
    """The TSTInfo's optional `ordering` and `nonce`, in pieces that end where
    the code's paths meet."""
    g = Gen("Tst4" + kind)
    params = tst_start(g)
    start_, end, title, what = TST4_DOC[kind]
    at = {"0x28DA": 0x28E2, "0x2918": 0x2920}.get(start_)
    if kind in ("e0", "e1"):
        params.append("(hrl : rl = 0)")
        tst4_peek(g, at)
        g.branch(at + 2, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hrl")
    elif kind in ("o", "x0", "x1"):
        params.append("(hrl : rl ≠ 0)")
        if kind != "x1":
            params.append(f"(hb1 : M0 rp {'=' if kind == 'o' else '≠'} BitVec.ofNat 8 1)")
        tst4_peek(g, at)
        g.branch(at + 2, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hrl")
        g.block(at + 4, at + 0xC)
        g.load(at + 0xC, "lw")
        g.load_in(at + 0xE, "rd_in", "(toNat_pos_of_ne hrl)")
        if kind == "o":
            g.block(0x28F4, 0x28F6)
            g.branch(0x28F6, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bne_byte_f (by decide) hb1")
            g.block(0x28FA, 0x2902)
            kb, ex, rd = g.boolt(0x2902, 0x1320)
            g.emit(f"  obtain ⟨r{kb}, hr{kb}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
            g.emit(f"  rcases r{kb} with eb{kb} | ⟨⟩")
            g.sc.append(("eq", ex, ".ok ()", [], f"hr{kb}"))

            def bad_bool(sub):
                sub.emit(f"  have g{kb}_10 : reg n{kb} a0 = (derErrByte eb{kb}).zeroExtend 32 := by rw [a0_{kb}, hr{kb}]; rfl")
                sub.regs[10] = ("U", f"(derErrByte eb{kb}).zeroExtend 32")
                sub.frame_after(kb, [(0x1328, 8)], {})
                sub.block(0x290A, 0x290C)
                sub.block(0x290C, 0x2910)
                sub.block(0x2910, 0x2914)
                sub.branch(0x2914, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t (derErr_ff_ne eb{kb})")
                sub.fail(sub.fail_proof(("eq", f"hr{kb}")), "sv_fail_2c60")
            g.fork(bad_bool)
            g.emit(f"  have g{kb}_10 : reg n{kb} a0 = BitVec.ofNat 32 0xFFFFFFFF := by rw [a0_{kb}, hr{kb}]; rfl")
            g.regs[10] = ("C", 0xFFFFFFFF)
            rp, rl, inp = rd
            tb = f"tb{kb}"
            g.emit(f"  obtain ⟨{tb}, htb{kb}⟩ := bool_ok_elem hr{kb}")
            L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
            g.sc.append(("eq", f"derElement 1 {L}", f".ok {tb}", [tb], f"htb{kb}"))
            g.emit(f"  obtain ⟨d8_{kb}, d12_{kb}⟩ := A{kb} {tb} htb{kb}")
            hl = f"BitVec.ofNat 32 ({tb}.header + {tb}.len)"
            g.frame_after(kb, [(0x1328, 8)], {0x1328: (f"({rp}) + {hl}", f"d8_{kb}"), 0x132C: (f"({rl}) - {hl}", f"d12_{kb}")})
            g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW htb{kb})"
            g.block(0x290A, 0x2914)
            g.branch(0x2914, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        elif kind == "x0":
            g.block(0x28F4, 0x28F6)
            g.branch(0x28F6, True, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bne_byte_t (by decide) hb1")
    else:
        g.regs[10] = ("U", "(M0 rp).zeroExtend 32")
        params.insert(0, "(g0_10 : reg n0 a0 = (M0 rp).zeroExtend 32)")
        params.append("(hrl : rl ≠ 0)")
        params.append(f"(hb2 : M0 rp {'≠' if kind == 'nn' else '='} BitVec.ofNat 8 2)")
        g.block(0x2932, 0x2934)
        if kind == "nn":
            g.branch(0x2934, True, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bne_byte_t (by decide) hb2")
        else:
            g.branch(0x2934, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bne_byte_f (by decide) hb2")
            g.block(0x2938, 0x2944)
            ki, ex, rd = g.intc(0x2944, 0x420, 0x1320)
            g.emit(f"  obtain ⟨r{ki}, hr{ki}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
            g.emit(f"  rcases r{ki} with ei{ki} | ⟨ip{ki}, il{ki}⟩")
            g.sc.append(("eq", ex, f".ok (ip{ki}, il{ki})", [f"ip{ki}", f"il{ki}"], f"hr{ki}"))

            def bad_int(sub):
                sub.emit(f"  obtain ⟨z{ki}, -⟩ := Er{ki} ei{ki} hr{ki}")
                sub.frame_after(ki, [(0x420, 8), (0x1328, 8)], {0x420: ("0", f"z{ki}")})
                sub.load(0x294C, "lw")
                sub.branch(0x2950, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; rfl")
                sub.load_any(0x2994)
                sub.jump(0x2998)
                sub.fail(sub.fail_proof(("eq", f"hr{ki}")), "sv_fail_2c60")
            g.fork(bad_int)
            rp, rl, inp = rd
            g.emit(f"  obtain ⟨ti{ki}, hti{ki}⟩ := int_ok_elem hr{ki}")
            L = f"(memBytes M0 ({rp}) ({rl}).toNat)"
            g.sc.append(("eq", f"derElement 2 {L}", f".ok ti{ki}", [f"ti{ki}"], f"hti{ki}"))
            g.emit(f"  obtain ⟨p0_{ki}, p4_{ki}⟩ := Ok{ki} ip{ki} il{ki} hr{ki}")
            g.emit(f"  obtain ⟨d8_{ki}, d12_{ki}⟩ := A{ki} ti{ki} hti{ki}")
            hl = f"BitVec.ofNat 32 (ti{ki}.header + ti{ki}.len)"
            g.frame_after(ki, [(0x420, 8), (0x1328, 8)],
                          {0x420: (f"ip{ki}", f"p0_{ki}"), 0x424: (f"il{ki}", f"p4_{ki}"),
                           0x1328: (f"({rp}) + {hl}", f"d8_{ki}"), 0x132C: (f"({rl}) - {hl}", f"d12_{ki}")})
            g.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hti{ki})"
            g.load(0x294C, "lw")
            g.branch(0x2950, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ({inp}.int_ne hr{ki})")
    keep_regs = TST_KEEP + ([10] if end == 0x2932 else [])
    keep = set(g.words) - {0x420, 0x424, 0x428, 0x42C, 0x430}
    stmt, proof = finish(g, end, sorted(keep_regs), keep, set())
    info = {"name": "sv_tst4" + kind, "title": title, "doc": f"From {start_} to 0x{end:X}: {what}",
            "params": params, "stmt": stmt, "proof": proof, "binders": TST2_BINDERS, "start": int(start_, 16),
            "import": "C3BootProofs.Proofs.SvGt"}
    return g, info


def stage_tst5(tag, present):
    """From 0x2952: the optional `[0]` TSA name (to 0x2970), or from 0x2970 the
    optional `[1]` extensions and the TSTInfo's end (to 0x29AA)."""
    g = Gen(f"Tst{5 if tag == 0xA0 else 6}" + ("s" if present else "n"))
    params = tst_start(g)
    params.append(f"(hce : derOptRes 0x{tag:X} (memBytes M0 (rp) (rl).toNat) {'≠' if present else '='} none)")
    if tag == 0xA0:
        g.block(0x2952, 0x2962)
        tst_opt(g, 0x2962, 0x1320, 0xA0, present, 0x296A)
        end = 0x2970
    else:
        g.block(0x2970, 0x2980)
        tst_opt(g, 0x2980, 0x1320, 0xA1, present, 0x2988, inverted=True)
        g.block(0x299A, 0x29A2)
        g.load(0x29A2, "lw")
        rem = lean_val(g.regs[10])

        def trailing(sub):
            sub.branch(0x29A4, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f hend")
            sub.block(0x29A6, 0x29A8)
            sub.jump(0x29A8)
            sub.fail(sub.fail_proof(("prop", "hend")), "sv_fail_2c60")
        g.prop_check(f"{rem} = 0", "hend", trailing)
        g.branch(0x29A4, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hend")
        end = 0x29AA
    keep = set(g.words) - {0x424, 0x428, 0x42C, 0x430}
    stmt, proof = finish(g, end, TST_KEEP, keep, set())
    if tag == 0xA0:
        title, doc = "the TSTInfo's TSA name", "the TSTInfo's optional `[0]` TSA name is " + (
            "present and well formed." if present else "absent.")
    else:
        title, doc = "the TSTInfo's extensions", "the TSTInfo's optional `[1]` extensions are " + (
            "present and well formed" if present else "absent") + ", and nothing follows."
    info = tst_opt_info(f"sv_tst{5 if tag == 0xA0 else 6}" + ("s" if present else "n"), 0, end, present, title,
                        f"From 0x{0x2952 if tag == 0xA0 else 0x2970:X} to 0x{end:X}: {doc}")
    info.update({"params": params, "stmt": stmt, "proof": proof, "start": 0x2952 if tag == 0xA0 else 0x2970})
    return g, info


TSV_BINDERS = ("{B out bp x21 x26 dg dp : Word} {sr ss : Bytes} "
               + "{" + " ".join(f"w{e:x}" for e in TST_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def stage_tsv():
    """From 0x29AA to the TSA loop at 0x2A40: the parsed timestamp's fields."""
    g = Gen("Tsv")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            25: ("U", "(BitVec.ofNat 8 (sr.getD 0 0)).zeroExtend 32", "BitVec.ofNat 8 (sr.getD 0 0)"),
            8: ("C", 0x18), 20: ("S", 0x1320), 22: ("U", "dp")}
    words = {e: f"w{e:x}" for e in TST_WORDS}
    params = start(g, regs, words, {})
    g.ranges[0x1020] = (47, "BitVec.ofNat 8 (sr.getD (1 + j) 0)")
    g.ranges[0x104F] = (48, "BitVec.ofNat 8 (ss.getD j 0)")
    params += ["(q0_1020 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))",
               "(q0_104f : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x104F + j)) = BitVec.ofNat 8 (ss.getD j 0))",
               "(h70 : w70 ≠ 0)"]
    g.block(0x29AA, 0x29BE)
    g.mc(0x29BE, 0x1480, 0x1020, 0x5F)
    g.load(0x29C6, "lw")
    g.branch(0x29C8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f h70")
    g.block(0x29CA, 0x29D6)
    k = g.k
    g.emit(f"  rw [shr_shr] at g{k}_11 g{k}_12")
    g.regs[11] = ("U", "(x21) >>> (8 + 8)")
    g.regs[12] = ("U", "(x21) >>> (8 + 16)")
    for o in (0x29D6, 0x29DA, 0x29DE):
        g.store(o, "sb")
    g.load(0x29E2, "lw")
    g.block(0x29E4, 0x29E6)
    g.store(0x29E6, "sw")
    g.block(0x29E8, 0x29F0)
    for o in (0x29F0, 0x29F4, 0x29F8):
        g.load(o, "lw")
        g.store(o + 2, "sw")
    g.store(0x29FC, "sb")
    g.block(0x2A00, 0x2A14)
    g.mc(0x2A14, 0xA41, 0x1480, 0x5F)
    g.store(0x2A1C, "sw")
    g.store(0x2A20, "sw")
    g.load(0x2A24, "lw")
    g.store(0x2A26, "sw")
    g.store(0x2A28, "sb")
    k = g.k
    for e, sh in ((0xA25, 8), (0xA26, 16), (0xA27, 24)):
        val = f"((x21) >>> {sh}).extractLsb' 0 8"
        g.emit(f"  have bs{k}_{e:x} : {g.byte_stmt(k, e, val)} := b{k}_{e:x}")
    g.emit(f"  have w{k}_a24 : {g.word_stmt(k, 0xA24, ('U', 'x21'))} := ld_of_shr_bytes b{k}_a24")
    for i in (1, 2, 3):
        g.emit(f"    (by rw [show {fa(0xA24)} + {i} = {fa(0xA24 + i)} by sv_addr]; exact bs{k}_{0xA24 + i:x})")
    g.words[0xA24] = ("U", "x21")
    for i in range(4):
        g.bytes.pop(0xA24 + i, None)
    for o in (0x2A2C, 0x2A30):
        g.load(o, "lw")
        g.store(o + 2, "sw")
    g.load(0x2A34, "lw")
    g.block(0x2A36, 0x2A3A)
    g.store(0x2A3A, "sw")
    g.block(0x2A3C, 0x2A40)
    stmt, proof = finish(g, 0x2A40, [2, 3, 4, 9, 18, 19, 21, 22, 23, 24, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_tsv", "title": "the parsed timestamp",
            "doc": "From 0x29AA to the TSA loop at 0x2A40: `sigstore::verify` copies the timestamp's fields, with "
            "the signature's `r` and `s`, into its `Timestamp` at offset 0xA20 of the frame, and points the "
            "loop at the trust root's TSA keys.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSV_BINDERS, "start": 0x29AA,
            "import": "C3BootProofs.Proofs.SvGt"}
    return g, info


TL_STRUCT = {0xA20: "w70", 0xA24: "x21", 0xA28: "w5c", 0xA2C: "w48", 0xA30: "w44", 0xA34: "w60", 0xA38: "w3c",
             0xA3C: "w78", 0xAA0: "dp", 0xAA4: "dg"}
TL_BINDERS = ("{B out bp x21 x26 dg dp c q sid slen : Word} {sr ss : Bytes} "
              + "{" + " ".join(f"w{e:x}" for e in TST_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")
TL_KEEP_REGS = [2, 3, 4, 9, 18, 19, 21, 22, 23, 24, 26, 27]


def tl_start(g):
    """The TSA loop's head at 0x2A40: `s1` counts down the bytes of entries
    left, and the word at 0x74 points 0x20 bytes before the next entry."""
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            22: ("U", "dp"), 23: ("S", 0xA40), 9: ("U", "c")}
    words = {e: f"w{e:x}" for e in TST_WORDS}
    words.update({0x74: "q"})
    words.update(TL_STRUCT)
    params = start(g, regs, words, {})
    g.bytes[0xA40] = "BitVec.ofNat 8 (sr.getD 0 0)"
    g.ranges[0xA41] = (47, "BitVec.ofNat 8 (sr.getD (1 + j) 0)")
    g.ranges[0xA70] = (48, "BitVec.ofNat 8 (ss.getD j 0)")
    params += ["(b0_a40 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (sr.getD 0 0))",
               "(q0_a41 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA41 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))",
               "(q0_a70 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA70 + j)) = BitVec.ofNat 8 (ss.getD j 0))"]
    return params


TL_PARAMS = ["(hc : c ≠ 0)", "(hsid : memLoad32 M0 (q + 0x20) = sid)",
             "(hslen : memLoad32 M0 (q + 0x24) = slen)", "(es_in : SvIn B (q + 0x20) 4)",
             "(el_in : SvIn B (q + 0x24) 4)",
             "(a_sid : (q + 0x20).toNat % 4 = 0)", "(a_slen : (q + 0x24).toNat % 4 = 0)",
             "(s_in : SvIn B sid slen.toNat)", "(i_in : SvIn B w5c w48.toNat)"]
TL_EQ = "memBytes M0 sid slen.toNat = memBytes M0 w5c w48.toNat"


def tl_entry(g):
    """From 0x2A40 to the comparison at 0x2A5A, for an entry with a signer ID."""
    g.branch(0x2A40, False, f"by rw [g{g.k}_9, s{g.k}.zero]; exact br_beq_f hc")
    g.load(0x2A42, "lw")
    g.load_mem(0x2A44, "sid", "hsid", "es_in", "a_sid")
    hz = f"hz_{g.k}"

    def null(sub):
        sub.branch(0x2A48, True, f"by rw [g{sub.k}_20, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not {hz})")
        sub.fail(sub.fail_proof(("prop", hz)), "sv_fail_2a82")
    g.prop_check("sid ≠ 0", hz, null)
    g.branch(0x2A48, False, f"by rw [g{g.k}_20, s{g.k}.zero]; exact br_beq_f {hz}")
    g.load(0x2A4C, "lw")
    g.load_mem(0x2A4E, "slen", "hslen", "el_in", "a_slen")
    g.block(0x2A52, 0x2A56)
    g.load(0x2A56, "lw")
    g.load(0x2A58, "lw")
    return g.seqeq(0x2A5A, "sid", "slen.toNat", "w5c", "w48.toNat", "(.inl s_in)", "(.inl i_in)",
                   f"(by rw [g{g.k}_13, ofNat_toNat_self])", f"(by rw [g{g.k}_11, ofNat_toNat_self])")


def stage_tl(kind):
    """The TSA loop at 0x2A40: an entry whose signer ID isn't the timestamp's
    ("miss", back to 0x2A40), the entry that is ("hit", to 0x2A94), or no
    entries left ("end")."""
    g = Gen("Tl" + kind)
    params = tl_start(g)
    if kind == "end":
        params.append("(hc : c = 0)")

        def none(sub):
            sub.branch(0x2A40, True, f"by rw [g{sub.k}_9, s{sub.k}.zero]; exact br_beq_t hc")
            sub.fail(sub.fail_proof(("prop", "hf")), "sv_fail_2a82")
        g.prop_check("False", "hf", none)
        stmt, _ = finish(g, 0x2A40, [2], set(), set())
        g.emit("  exact hf.elim")
        proof = ""
        title, doc = "no TSA key left", ("The TSA loop at 0x2A40 with no entries left: no listed TSA key has the "
                                          "timestamp's signer ID, and `sigstore::verify` fails.")
    else:
        params += TL_PARAMS + [f"(hm : {'¬ ' if kind == 'miss' else ''}{TL_EQ})"]
        ke = tl_entry(g)
        g.set_a0(ke, 0 if kind == "miss" else 1, f"ite_eq_{'right' if kind == 'miss' else 'left'} hm")
        g.block(0x2A62, 0x2A64)
        g.block(0x2A64, 0x2A68)
        g.store(0x2A68, "sw")
        if kind == "miss":
            g.branch(0x2A6A, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            end, keep_regs = 0x2A40, TL_KEEP_REGS
            title, doc = "a TSA key that didn't sign the timestamp", (
                "One pass of the TSA loop, from 0x2A40 back to it, for a listed TSA key whose signer ID isn't the "
                "timestamp's.")
        else:
            g.branch(0x2A6A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            g.load(0x2A6C, "lw")
            g.load(0x2A6E, "lw")
            g.block(0x2A70, 0x2A74)
            kn = g.sne(0x2A74, "w5c", "w48.toNat", "sid", "slen.toNat", "(.inl i_in)", "(.inl s_in)",
                       f"(by rw [g{g.k}_11, ofNat_toNat_self])", f"(by rw [g{g.k}_13, ofNat_toNat_self])")
            g.set_a0(kn, 0, "ite_eq_left hm.symm")
            g.branch(0x2A7C, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            end, keep_regs = 0x2A94, TL_KEEP_REGS + [8, 20, 25]
            title, doc = "the TSA key that signed the timestamp", (
                "The TSA loop's end, from 0x2A40 to 0x2A94, at a listed TSA key whose signer ID is the timestamp's.")
        stmt, proof = finish(g, end, sorted(keep_regs), set(g.words), set(g.bytes))
    info = {"name": "sv_tl" + kind, "title": title, "doc": doc,
            "params": params, "stmt": stmt, "proof": proof, "binders": TL_BINDERS, "start": 0x2A40,
            "import": "C3BootProofs.Proofs.SvGt"}
    return g, info


TSIG_BINDERS = TL_BINDERS.replace("c q sid slen : Word}", "q sid slen : Word}")


def tsig_start(g):
    """After the TSA loop's hit at 0x2A94: the word at 0x74 points at the
    entry, and `s4` and `s9` hold its signer ID."""
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            22: ("U", "dp"), 23: ("S", 0xA40)}
    words = {e: f"w{e:x}" for e in TST_WORDS}
    words.update({0x74: "q"})
    words.update(TL_STRUCT)
    params = start(g, regs, words, {})
    g.bytes[0xA40] = "BitVec.ofNat 8 (sr.getD 0 0)"
    g.ranges[0xA41] = (47, "BitVec.ofNat 8 (sr.getD (1 + j) 0)")
    g.ranges[0xA70] = (48, "BitVec.ofNat 8 (ss.getD j 0)")
    params += ["(b0_a40 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (sr.getD 0 0))",
               "(q0_a41 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA41 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))",
               "(q0_a70 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA70 + j)) = BitVec.ofNat 8 (ss.getD j 0))",
               "(S2 : SvSha2Code M0)", "(KS : SvK2Sep B)",
               "(tst_in : SvIn B w70 x21.toNat)", "(dg_in : SvIn B dg 32)", "(sig_in : SvIn B w68 w64.toNat)",
               "(dp_in : SvIn B dp 32)", "(sa_in : SvIn B w44 w60.toNat)"]
    return params


def stage_tsig():
    """From 0x2A94 to the TSA's signature check at 0x2B16: the token's
    digests, and the hash of its signed attributes."""
    g = Gen("Tsig")
    params = tsig_start(g)
    g.load(0x2A94, "lw")
    g.block(0x2A98, 0x2A9C)
    g.load(0x2A9C, "lw")
    g.sha256(0x2A9E, 0x420, "w70", "(x21).toNat", "(.inl tst_in)", f"(by rw [g{g.k}_12, ofNat_toNat_self])",
             "(by have := tst_in.lo; omega)")
    g.block(0x2AA6, 0x2AAC)
    g.carry_digest()
    ka = g.a32ne(0x2AAC, 0x420, "dg", "(.inl dg_in)")
    eq1 = "sha256 (memBytes M0 (w70) (x21).toNat) = memBytes M0 dg 32"

    def bad_tst(sub):
        sub.set_a0(ka, 1, "ite_eq_right htd")
        sub.block(0x2AB4, 0x2AB6)
        sub.branch(0x2AB6, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", "htd")), "sv_fail_2c60")
    g.prop_check(eq1, "htd", bad_tst)
    g.set_a0(ka, 0, "ite_eq_left htd")
    g.block(0x2AB4, 0x2AB6)
    g.branch(0x2AB6, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x2ABA, 0x2ABE)
    g.load(0x2ABE, "lw")
    g.load(0x2AC0, "lw")
    g.sha256(0x2AC2, 0x420, "w68", "(w64).toNat", "(.inl sig_in)", f"(by rw [g{g.k}_12, ofNat_toNat_self])",
             "(by have := sig_in.lo; omega)")
    g.block(0x2ACA, 0x2AD0)
    g.carry_digest()
    kb = g.a32ne(0x2AD0, 0x420, "dp", "(.inl dp_in)")
    eq2 = "sha256 (memBytes M0 (w68) (w64).toNat) = memBytes M0 dp 32"

    def bad_imprint(sub):
        sub.set_a0(kb, 1, "ite_eq_right him")
        sub.branch(0x2AD8, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", "him")), "sv_fail_2c60")
    g.prop_check(eq2, "him", bad_imprint)
    g.set_a0(kb, 0, "ite_eq_left him")
    g.branch(0x2AD8, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load(0x2ADC, "lw")

    def empty_attrs(sub):
        sub.branch(0x2ADE, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not hsa)")
        sub.block(0x2C5A, 0x2C5C)
        sub.jump(0x2C5C)
        sub.fail(sub.fail_proof(("prop", "hsa")), "sv_fail_2c60")
    g.prop_check("w60 ≠ 0", "hsa", empty_attrs)
    g.branch(0x2ADE, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hsa")
    g.pinned.add("hsa")
    g.load(0x2AE2, "lw")
    g.block(0x2AE4, 0x2AE6)
    g.load(0x2AE6, "lw")
    g.block(0x2AE8, 0x2AEA)
    g.block(0x2AEA, 0x2AF2)
    g.block(0x2AF2, 0x2AF8)
    for o in (0x2AF8, 0x2AFA, 0x2AFC, 0x2AFE):
        g.store(o, "sw")
    g.block(0x2B00, 0x2B0E)
    p1 = lean_val(g.words[0x1028])
    l1w = lean_val(g.words[0x102C])
    g.parts2(0x2B0E, 0x420, 0x1020, "BitVec.ofNat 32 0x3FCC486D", "1", "(.inr ⟨by decide, by decide⟩)",
             p1, f"({l1w}).toNat", "(sa_drop1 sa_in hsa)",
             f"w{g.k}_1024", f"(by rw [w{g.k}_102c, ofNat_toNat_self])", "(by decide)", "(sa_drop1_lt sa_in hsa)")
    kd, oc, ex = g.digest
    g.extra.append((f"memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x{oc:X}) 32 = {ex}", f"D{kd}"))
    stmt, proof = finish(g, 0x2B16, TL_KEEP_REGS, set(g.words), set(g.bytes))
    info = {"name": "sv_tsig", "title": "the timestamp's digests",
            "doc": "From 0x2A94 to 0x2B16: SHA-256 of the TSTInfo is the signed `messageDigest`, SHA-256 of the "
            "image signature is the TSTInfo's message imprint, the signed attributes aren't empty, and the "
            "frame at offset 0x420 holds SHA-256 of the signed attributes with their first byte replaced by 0x31.",
            "params": params, "stmt": stmt, "proof": proof, "binders": TSIG_BINDERS, "start": 0x2A94,
            "import": "C3BootProofs.Proofs.SvSha2"}
    return g, info


CK_BINDERS = ("{B out bp x21 x26 dg dp pv q ckp ckl : Word} "
              + "{" + " ".join(f"w{e:x}" for e in TST_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def ck_line_tail(lw_off, reg, sw_off=None):
    def tail(sub):
        sub.load(lw_off, "lw")
        if sw_off is not None:
            sub.store(sw_off, "sw")
        br = sw_off + 2 if sw_off is not None else lw_off + 4
        sub.branch(br, True, f"by rw [g{sub.k}_{reg}, s{sub.k}.zero]; rfl")
    return tail


def stage_ck1():
    """From 0x2B34 to 0x2BCA: the TSA's signature checked, and the
    checkpoint's origin, size, and root lines and the blank line after them."""
    g = Gen("Ck1")
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            22: ("U", "dp"), 23: ("S", 0xA40), 10: ("U", "pv")}
    words = {e: f"w{e:x}" for e in TST_WORDS}
    words.update({0x74: "q"})
    words.update(TL_STRUCT)
    params = start(g, regs, words, {})
    params += ["(CK0 : SvCkCode M0)", "(hckp : memLoad32 M0 (bp + 0x18) = ckp)",
               "(hckl : memLoad32 M0 (bp + 0x1C) = ckl)", "(ckp_in4 : SvIn B (bp + 0x18) 4)",
               "(ckl_in4 : SvIn B (bp + 0x1C) 4)", "(a_ckp : (bp + 0x18).toNat % 4 = 0)",
               "(a_ckl : (bp + 0x1C).toNat % 4 = 0)", "(ck_in : SvIn B ckp ckl.toNat)"]

    def bad_sig(sub):
        sub.branch(0x2B34, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not hv)")
        sub.block(0x2C5E, 0x2C60)
        sub.fail(sub.fail_proof(("prop", "hv")), "sv_fail_2c60")
    g.prop_check("pv ≠ 0", "hv", bad_sig)
    g.branch(0x2B34, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hv")
    g.load_mem(0x2B38, "ckp", "hckp", "ckp_in4", "a_ckp")
    g.load_mem(0x2B3C, "ckl", "hckl", "ckl_in4", "a_ckl")
    g.block(0x2B40, 0x2B44)
    g.store(0x2B44, "sw")
    g.block(0x2B46, 0x2B48)
    k0, ix0, p1, n1, in1 = g.line(0x2B48, 0x420, "ckp", "(ckl).toNat", "(.inl ck_in)",
                                  f"(by rw [g{g.k}_12, ofNat_toNat_self])", ck_line_tail(0x2B50, 10, 0x2B54))
    g.load(0x2B50, "lw")
    g.store(0x2B54, "sw")
    g.branch(0x2B56, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f ck_in.pos_ne")
    rest = (p1, n1, in1, k0)
    lines = [(0x2B5A, 0x2B6A, 0x2B72, 9), (0x2B7A, 0x2B88, 0x2B90, 23), (0x2B98, 0x2BA8, 0x2BB0, 10)]
    ks = []
    for (blk, call, lw, reg) in lines:
        p, nl, inp, kp = rest
        g.block(blk, blk + 4)
        if blk == 0x2B5A:
            g.load(0x2B5E, "lw")
            g.store(0x2B60, "sw")
            g.load(0x2B62, "lw")
            g.load(0x2B64, "lw")
            g.block(0x2B66, 0x2B6A)
        else:
            g.load(blk + 4, "lw")
            g.load(blk + 6 if blk == 0x2B7A else blk + 8, "lw")
            g.load(blk + 8 if blk == 0x2B7A else blk + 0xA, "lw")
            g.block(blk + 0xA if blk == 0x2B7A else blk + 0xC, call)
        ha2 = f"(by rw [g{g.k}_12, sub_ofNat (Nat.succ_le_of_lt hix{kp}) (by omega)])"
        k, ix, p2, n2, in2 = g.line(call, 0x420, p, nl, inp, ha2, ck_line_tail(lw, reg))
        ks.append((k, ix, p, nl, inp))
        g.load(lw, "lw")
        g.branch(lw + 4, False, f"by rw [g{g.k}_{reg}, s{g.k}.zero]; exact br_beq_f {inp}.ne0")
        rest = (p2, n2, in2, k)
    k3, ix3 = ks[-1][0], ks[-1][1]
    g.load(0x2BB8, "lw")

    def not_blank(sub):
        sub.branch(0x2BBC, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t hblank")
        sub.block(0x2FF2, 0x2FF4)
        sub.jump(0x2FF4)
        sub.fail(sub.fail_proof(("prop", "hblank")))
    g.prop_check(f"BitVec.ofNat 32 {ix3} = 0", "hblank", not_blank)
    g.branch(0x2BBC, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f hblank")
    g.load(0x2BC0, "lw")
    g.store(0x2BC4, "sw")
    sig = lean_val(g.regs[10])

    def no_sig(sub):
        sub.branch(0x2BC6, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not hsig)")
        sub.block(0x2FF2, 0x2FF4)
        sub.jump(0x2FF4)
        sub.fail(sub.fail_proof(("prop", "hsig")))
    g.prop_check(f"{sig} ≠ 0", "hsig", no_sig)
    g.branch(0x2BC6, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hsig")
    keep = set(g.words) - {0x420, 0x424}
    stmt, proof = finish(g, 0x2BCA, [2, 3, 4, 8, 9, 18, 19, 21, 22, 23, 24, 25, 26, 27], keep, set())
    info = {"name": "sv_ck1", "title": "the checkpoint's lines",
            "doc": "From 0x2B34 to 0x2BCA: the TSA's signature checked, and the checkpoint splits into an origin "
            "line, a size line, a root line, a blank line, and a nonempty rest.",
            "params": params, "stmt": stmt, "proof": proof, "binders": CK_BINDERS, "start": 0x2B34,
            "import": "C3BootProofs.Proofs.SvCkpt"}
    return g, info


CK2_BINDERS = ("{B out bp x21 x26 dg q ckl sl sp1 rl rp sgp : Word} "
               + "{" + " ".join(f"w{e:x}" for e in TST_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def ck_fail_2ff2(sub, hname):
    sub.block(0x2FF2, 0x2FF4)
    sub.jump(0x2FF4)
    sub.fail(sub.fail_proof(("prop", hname)))


def ck2_start(g):
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            8: ("U", "sl"), 9: ("U", "sp1"), 22: ("U", "rl"), 23: ("U", "rp"), 25: ("U", "ckl")}
    words = {e: f"w{e:x}" for e in TST_WORDS}
    words.update({0x74: "q", 0x428: "sgp"})
    words.update(TL_STRUCT)
    return start(g, regs, words, {})


def stage_ck2(lead):
    """From 0x2BCA to the size's digit loop at 0x2C06: the signature section
    fits in the checkpoint, the size line has 1 to 20 bytes, and a size of
    more than one digit doesn't start with `0`."""
    g = Gen("Ck2" + ("b" if lead else "a"))
    g.generic_alu = True
    params = ck2_start(g)
    params += ["(sz_in : SvIn B sp1 sl.toNat)", f"(hsl : {'' if lead else '¬ '}1 < sl.toNat)"]
    g.load(0x2BCA, "lw")

    def big(sub):
        sub.branch(0x2BCC, True, f"by rw [g{sub.k}_10, g{sub.k}_25]; exact br_bgeu_t hc1")
        ck_fail_2ff2(sub, "hc1")
    g.prop_check("w5c.toNat < ckl.toNat", "hc1", big)
    g.branch(0x2BCC, False, f"by rw [g{g.k}_10, g{g.k}_25]; exact br_bgeu_f hc1")
    g.load(0x2BD0, "lw")
    g.block(0x2BD2, 0x2BD6)
    g.block(0x2BD6, 0x2BD8)
    g.store(0x2BD8, "sw")
    body = lean_val(g.regs[10])

    def neg(sub):
        sub.branch(0x2BDA, True, f"by rw [g{sub.k}_25, g{sub.k}_10]; exact br_bltu_t (Decidable.of_not_not hc2)")
        ck_fail_2ff2(sub, "hc2")
    g.prop_check(f"¬ (ckl).toNat < ({body}).toNat", "hc2", neg)
    g.branch(0x2BDA, False, f"by rw [g{g.k}_25, g{g.k}_10]; exact br_bltu_f hc2")
    g.block(0x2BDE, 0x2BE2)
    g.block(0x2BE2, 0x2BE4)
    d = lean_val(g.regs[10])

    def size_len(sub):
        sub.branch(0x2BE4, True, f"by rw [g{sub.k}_10, g{sub.k}_11]; exact br_bltu_t (Decidable.of_not_not hc3)")
        ck_fail_2ff2(sub, "hc3")
    g.prop_check(f"¬ ({d}).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat", "hc3", size_len)
    g.branch(0x2BE4, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bltu_f hc3")
    g.load(0x2BE8, "lw")
    g.store(0x2BEC, "sw")
    g.block(0x2BEE, 0x2BF0)
    if not lead:
        g.branch(0x2BF0, True, f"by rw [g{g.k}_10, g{g.k}_8]; exact br_bgeu_t hsl")
    else:
        g.branch(0x2BF0, False, f"by rw [g{g.k}_10, g{g.k}_8]; exact br_bgeu_f hsl")
        g.load_in(0x2BF4, "sz_in", "(by omega)")
        g.block(0x2BF8, 0x2BFC, {10: ("(M0 sp1).zeroExtend 32 + 0xFFFFFFD0",
                                      "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, svCk2b2bf8, upd, ↓reduceIte]; rw [g{p}_10]; rfl")})

        def zero(sub):
            sub.branch(0x2BFC, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t ((digit0_iff _).mpr (Decidable.of_not_not hlead))")
            ck_fail_2ff2(sub, "hlead")
        g.prop_check("M0 sp1 ≠ 0x30", "hlead", zero)
        g.branch(0x2BFC, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f fun e => hlead ((digit0_iff _).mp e)")
    g.store(0x2C00, "sw")
    g.store(0x2C02, "sw")
    g.block(0x2C04, 0x2C06)
    stmt, proof = finish(g, 0x2C06, [2, 3, 4, 8, 9, 10, 18, 19, 21, 22, 23, 24, 25, 26, 27], set(g.words), set())
    info = {"name": "sv_ck2" + ("b" if lead else "a"), "title": "the checkpoint's size line" + (", leading digit" if lead else ""),
            "doc": "From 0x2BCA to the size's digit loop at 0x2C06: the signature section is shorter than the "
            "checkpoint, the size line has 1 to 20 bytes" + (", and its first byte isn't `0`." if lead else
            ", and it has one byte."),
            "params": params, "stmt": stmt, "proof": proof, "binders": CK2_BINDERS, "start": 0x2BCA,
            "import": "C3BootProofs.Proofs.SvCkpt"}
    return g, info


CK_LOW = [0x8, 0xC, 0x10, 0x14, 0x18, 0x1C, 0x20]
CKD_BINDERS = ("{B out bp x21 x26 dg q ckl c p rl rp sgp : Word} "
               + "{" + " ".join(f"w{e:x}" for e in CK_LOW + TST_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")


def ckd_start(g):
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            8: ("U", "c"), 9: ("U", "p"), 22: ("U", "rl"), 23: ("U", "rp"), 25: ("U", "ckl"), 10: ("C", 10)}
    words = {e: f"w{e:x}" for e in TST_WORDS}
    words.update({0x74: "q", 0x428: "sgp"})
    words.update(TL_STRUCT)
    words.update({e: f"w{e:x}" for e in CK_LOW})
    return start(g, regs, words, {})


def stage_ckd():
    """One pass of the size's digit loop, from 0x2C06 back to it: the next
    byte is a digit, and the size times ten plus the digit fits in 64 bits."""
    g = Gen("Ckd")
    g.generic_alu = True
    params = ckd_start(g) + ["(hc : c ≠ 0)", "(pin : SvIn B p c.toNat)"]
    g.branch(0x2C06, False, f"by rw [g{g.k}_8, s{g.k}.zero]; exact br_beq_f hc")
    g.load_in(0x2C08, "pin", "(toNat_pos_of_ne hc)")
    g.block(0x2C0C, 0x2C10)
    g.block(0x2C10, 0x2C14)
    d = lean_val(g.regs[11])

    def not_digit(sub):
        sub.branch(0x2C14, True, f"by rw [g{sub.k}_11, g{sub.k}_10]; exact br_bgeu_t hdig")
        ck_fail_2ff2(sub, "hdig")
    g.prop_check(f"({d}).toNat < (BitVec.ofNat 32 0xA).toNat", "hdig", not_digit)
    g.branch(0x2C14, False, f"by rw [g{g.k}_11, g{g.k}_10]; exact br_bgeu_f hdig")
    g.load(0x2C18, "lw")
    g.block(0x2C1A, 0x2C1E)
    g.load(0x2C1E, "lw")
    g.block(0x2C20, 0x2C24)
    g.block(0x2C24, 0x2C28)
    g.block(0x2C28, 0x2C2A)
    g.block(0x2C2A, 0x2C2E)
    g.block(0x2C2E, 0x2C32)
    g.block(0x2C32, 0x2C34)
    ov1 = lean_val(g.regs[13])

    def over1(sub):
        sub.branch(0x2C34, True, f"by rw [g{sub.k}_13, s{sub.k}.zero]; exact br_bne_t hov1")
        ck_fail_2ff2(sub, "hov1")
    g.prop_check(f"{ov1} = 0", "hov1", over1)
    g.branch(0x2C34, False, f"by rw [g{g.k}_13, s{g.k}.zero]; exact br_bne_f hov1")
    g.load(0x2C38, "lw")
    g.block(0x2C3A, 0x2C3E)
    g.block(0x2C3E, 0x2C40)
    g.store(0x2C40, "sw")
    g.block(0x2C42, 0x2C46)
    g.block(0x2C46, 0x2C4A)
    g.store(0x2C4A, "sw")
    g.block(0x2C4C, 0x2C50)
    g.block(0x2C50, 0x2C52)
    g.block(0x2C52, 0x2C54)
    g.block(0x2C54, 0x2C56)
    ov2 = lean_val(g.regs[11])

    def over2(sub):
        sub.branch(0x2C56, False, f"by rw [g{sub.k}_11, s{sub.k}.zero]; exact br_beq_f hov2")
        sub.jump(0x2C58)
        ck_fail_2ff2(sub, "hov2")
    g.prop_check(f"{ov2} = 0", "hov2", over2)
    g.branch(0x2C56, True, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_beq_t hov2")
    stmt, proof = finish(g, 0x2C06, [2, 3, 4, 8, 9, 10, 18, 19, 21, 22, 23, 24, 25, 26, 27], set(g.words), set())
    info = {"name": "sv_ckd", "title": "a digit of the checkpoint's size",
            "doc": "One pass of the size's digit loop, from 0x2C06 back to it: the next byte is a decimal digit, and "
            "the 64-bit size at offsets 0x60 and 0x70 times ten plus the digit doesn't overflow.",
            "params": params, "stmt": stmt, "proof": proof, "binders": CKD_BINDERS, "start": 0x2C06,
            "import": "C3BootProofs.Proofs.SvCkpt"}
    return g, info


def cke_tail(g, bad):
    """From 0x2CA2: the decoder's error flag, then its length against 32."""
    g.block(0x2CA2, 0x2CAA)
    g.load(0x2CAA, "lbu")
    if bad == "flag":
        g.branch(0x2CAE, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        return
    g.branch(0x2CAE, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x2CB2, 0x2CBA)
    g.load(0x2CBA, "lw")
    g.block(0x2CBC, 0x2CBE)


def stage_cke():
    """From the size's digit loop's end at 0x2C06 to the log loop at 0x2CE2:
    the size fits in 63 bits, and the root line is the base64 of 32 bytes."""
    g = Gen("Cke")
    g.generic_alu = True
    params = ckd_start(g) + ["(hc : c = 0)", "(CK0 : SvCkCode M0)", "(rt_in : SvIn B rp rl.toNat)"]
    g.branch(0x2C06, True, f"by rw [g{g.k}_8, s{g.k}.zero]; exact br_beq_t hc")
    g.load(0x2C6E, "lw")

    def big(sub):
        sub.branch(0x2C70, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_blt0_t hsz")
        ck_fail_2ff2(sub, "hsz")
    g.prop_check("w70.toNat < 2 ^ 31", "hsz", big)
    g.branch(0x2C70, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_blt0_f hsz")
    g.block(0x2C74, 0x2C7E)
    g.ms(0x2C7E, 0x420, 0x60)
    g.block(0x2C86, 0x2C9A)
    k, ex = g.b64(0x2C9A, 0x1380, 0x420, "rp", "(rl).toNat", "(.inl rt_in)", f"(by rw [g{g.k}_12, ofNat_toNat_self])", "0x60")
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{k} with _ | bs{k}")
    g.sc.append(("eq", ex, f"some bs{k}", [f"bs{k}"], f"hr{k}"))

    def none(sub):
        sub.emit(f"  have z{k} := Bad{k} fun b h => by rw [hr{k}] at h; cases h")
        sub.frame_after(k, [(0x1380, 8), (0x420, 0x60)], {}, {0x1380: ("(1 : BitVec 8)", f"z{k}")})
        cke_tail(sub, "flag")
        ck_fail_none(sub, ("eq", f"hr{k}"))
    g.fork(none)
    bs = f"bs{k}"
    hl = "hl32"

    def wrong_len(sub):
        sub.emit(f"  by_cases hle : {bs}.length ≤ 0x60")

        def long(s2):
            s2.emit(f"  have z{k} := Bad{k} fun b h => by rw [hr{k}] at h; cases h; omega")
            s2.frame_after(k, [(0x1380, 8), (0x420, 0x60)], {}, {0x1380: ("(1 : BitVec 8)", f"z{k}")})
            cke_tail(s2, "flag")
            ck_fail_none(s2, ("prop", hl))
        sub.emit("  rotate_left")
        sub.fork(long)
        sub.emit(f"  obtain ⟨b0_{k}, b4_{k}, -⟩ := Ok{k} {bs} hr{k} hle")
        sub.frame_after(k, [(0x1380, 8), (0x420, 0x60)], {0x1384: (f"BitVec.ofNat 32 {bs}.length", f"b4_{k}")},
                        {0x1380: ("(0 : BitVec 8)", f"b0_{k}")})
        cke_tail(sub, "len")
        sub.branch(0x2CBE, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t (ne32_add (by omega) {hl})")
        ck_fail_none(sub, ("prop", hl))
    g.prop_check(f"{bs}.length = 32", hl, wrong_len)
    g.emit(f"  obtain ⟨b0_{k}, b4_{k}, bm_{k}⟩ := Ok{k} {bs} hr{k} (by omega)")
    g.pinned |= {f"bm_{k}"}
    g.frame_after(k, [(0x1380, 8), (0x420, 0x60)], {0x1384: (f"BitVec.ofNat 32 {bs}.length", f"b4_{k}")},
                  {0x1380: ("(0 : BitVec 8)", f"b0_{k}")})
    g.ranges[0x420] = (32, f"BitVec.ofNat 8 ({bs}.getD j 0)")
    g.emit(f"  have q{k}_420 : ∀ j, j < 32 → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 ({bs}.getD j 0) :=")
    g.emit(f"    fun j hj => by rw [← add_ofNat_assoc]; exact memBytes_range bm_{k} j (by omega)")
    cke_tail(g, "len")
    g.branch(0x2CBE, False, f"by rw [g{g.k}_10, s{g.k}.zero, {hl}]; decide")
    g.load(0x2CC2, "lbu")
    g.store(0x2CC6, "sw")
    g.block(0x2CC8, 0x2CD0)
    g.mc(0x2CD0, 0x320, 0x421, 0x1F)
    g.load(0x2CD8, "lw")
    g.block(0x2CDA, 0x2CDE)
    g.block(0x2CDE, 0x2CE2)
    stmt, proof = finish(g, 0x2CE2, [2, 3, 4, 9, 18, 19, 21, 22, 23, 24, 25, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_cke", "title": "the checkpoint's root hash",
            "doc": "From the size's digit loop's end at 0x2C06 to the log loop at 0x2CE2: the size is below 2^63, "
            "and the root line is the base64 of 32 bytes, which go to the word at offset 0x1C and the 31 bytes "
            "at offset 0x320.",
            "params": params, "stmt": stmt, "proof": proof, "binders": CKD_BINDERS, "start": 0x2C06,
            "import": "C3BootProofs.Proofs.SvCkpt"}
    return g, info


def ck_fail_none(sub, why):
    sub.block(0x2FF2, 0x2FF4)
    sub.jump(0x2FF4)
    sub.fail(sub.fail_proof(why))


CL_BINDERS = ("{B out bp x21 x26 dg c q rl rp sgp op ol : Word} {rt : Bytes} "
              + "{" + " ".join(f"w{e:x}" for e in [0x8, 0xC, 0x10, 0x14, 0x18, 0x20] + TST_WORDS)
              + " : Word} {v : Nat → Word} {n0 : Machine}")
CL_KEEP_REGS = [2, 3, 4, 9, 18, 19, 21, 22, 23, 24, 25, 26, 27]


def cl_start(g):
    """The log loop's head at 0x2CE2: `s1` counts down the bytes of entries
    left and `s9` points 0x20 bytes before the next entry."""
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20), 24: ("U", "dg"),
            9: ("U", "c"), 22: ("U", "rl"), 23: ("U", "rp"), 25: ("U", "q")}
    words = {e: f"w{e:x}" for e in TST_WORDS}
    words.update({0x74: "q'", 0x428: "sgp", 0x1C: "(BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32"})
    words.pop(0x74)
    words.update(TL_STRUCT)
    words.update({e: f"w{e:x}" for e in (0x8, 0xC, 0x10, 0x14, 0x18, 0x20)})
    params = start(g, regs, words, {})
    g.ranges[0x320] = (31, "BitVec.ofNat 8 (rt.getD (1 + j) 0)")
    params += ["(q0_320 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))"]
    return params


CL_PARAMS = ["(hc : c ≠ 0)", "(horg : memLoad32 M0 (q + 0x20) = op)",
             "(hol : memLoad32 M0 (q + 0x24) = ol)", "(eo_in : SvIn B (q + 0x20) 4)",
             "(el_in : SvIn B (q + 0x24) 4)",
             "(a_op : (q + 0x20).toNat % 4 = 0)", "(a_ol : (q + 0x24).toNat % 4 = 0)",
             "(o_in : SvIn B op ol.toNat)", "(l_in : SvIn B w48 w44.toNat)"]
CL_EQ = "memBytes M0 op ol.toNat = memBytes M0 w48 w44.toNat"


def stage_cl(kind):
    """The log loop at 0x2CE2: a log whose origin isn't the checkpoint's
    ("miss", back to 0x2CE2), the log whose origin is ("hit", to 0x2D12), or
    no logs left ("end")."""
    g = Gen("Cl" + kind)
    params = cl_start(g)
    g.block(0x2CE2, 0x2CE4)
    if kind == "end":
        params.append("(hc : c = 0)")

        def none(sub):
            sub.branch(0x2CE4, False, f"by rw [g{sub.k}_9, s{sub.k}.zero]; exact br_bne_f hc")
            sub.jump(0x2CE6)
            sub.fail(sub.fail_proof(("prop", "hf")))
        g.prop_check("False", "hf", none)
        stmt, _ = finish(g, 0x2CE2, [2], set(), set())
        g.emit("  exact hf.elim")
        proof = ""
        title, doc = "no log left", ("The log loop at 0x2CE2 with no entries left: no listed log has the "
                                     "checkpoint's origin, and `sigstore::verify` fails.")
    else:
        params += CL_PARAMS + [f"(hm : {'¬ ' if kind == 'miss' else ''}{CL_EQ})"]
        g.branch(0x2CE4, True, f"by rw [g{g.k}_9, s{g.k}.zero]; exact br_bne_t hc")
        g.load_mem(0x2CEA, "op", "horg", "eo_in", "a_op")
        g.store(0x2CEE, "sw")
        hz = f"hz_{g.k}"

        def null(sub):
            sub.branch(0x2CF0, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_f (Decidable.of_not_not {hz})")
            sub.jump(0x2CF2)
            sub.fail(sub.fail_proof(("prop", hz)))
        g.prop_check("op ≠ 0", hz, null)
        g.branch(0x2CF0, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_t {hz}")
        g.load_mem(0x2CF6, "ol", "hol", "el_in", "a_ol")
        g.load(0x2CFA, "lw")
        g.block(0x2CFC, 0x2CFE)
        g.load(0x2CFE, "lw")
        g.load(0x2D00, "lw")
        ke = g.seqeq(0x2D02, "op", "ol.toNat", "w48", "w44.toNat", "(.inl o_in)", "(.inl l_in)",
                     f"(by rw [g{g.k}_13, ofNat_toNat_self])", f"(by rw [g{g.k}_11, ofNat_toNat_self])")
        g.set_a0(ke, 0 if kind == "miss" else 1, f"ite_eq_{'right' if kind == 'miss' else 'left'} hm")
        g.block(0x2D0A, 0x2D0C)
        g.block(0x2D0C, 0x2D10)
        if kind == "miss":
            g.branch(0x2D10, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            end = 0x2CE2
            title, doc = "a log that didn't sign the checkpoint", (
                "One pass of the log loop, from 0x2CE2 back to it, for a listed log whose origin isn't the "
                "checkpoint's.")
        else:
            g.branch(0x2D10, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            end = 0x2D12
            title, doc = "the log the checkpoint names", (
                "The log loop's end, from 0x2CE2 to 0x2D12, at a listed log whose origin is the checkpoint's.")
        stmt, proof = finish(g, end, CL_KEEP_REGS, set(g.words), set(g.bytes))
    info = {"name": "sv_cl" + kind, "title": title, "doc": doc,
            "params": params, "stmt": stmt, "proof": proof, "binders": CL_BINDERS, "start": 0x2CE2,
            "import": "C3BootProofs.Proofs.SvCkpt"}
    return g, info


def stage_cs1():
    """From the log's entry at 0x2D12 to the signature loop at 0x2D6E: the log
    key's hash, from the origin, a newline, the Ed25519 tag, and the key."""
    g = Gen("Cs1")
    params = cl_start(g)
    params += ["(S2 : SvSha2Code M0)", "(KS : SvK2Sep B)", "(hkp : memLoad32 M0 (q + 0x18) = kp)",
               "(hkw : memLoad32 M0 (q + 0x1C) = kw)", "(kp_in4 : SvIn B (q + 0x18) 4)", "(kw_in4 : SvIn B (q + 0x1C) 4)",
               "(a_kp : (q + 0x18).toNat % 4 = 0)", "(a_kw : (q + 0x1C).toNat % 4 = 0)",
               "(kp_in : SvIn B kp 32)", "(l_in : SvIn B w48 w44.toNat)"]
    g.block(0x2D12, 0x2D14)
    g.load_mem(0x2D14, "kp", "hkp", "kp_in4", "a_kp")
    g.load_mem(0x2D16, "kw", "hkw", "kw_in4", "a_kw")
    g.store(0x2D18, "sw")
    g.block(0x2D1A, 0x2D24)
    g.load(0x2D24, "lw")
    g.block(0x2D26, 0x2D2A)
    g.store(0x2D2A, "sw")
    g.load(0x2D2C, "lw")
    for o in (0x2D2E, 0x2D30, 0x2D32):
        g.store(o, "sw")
    g.block(0x2D34, 0x2D40)
    for o in (0x2D40, 0x2D42, 0x2D44, 0x2D46, 0x2D48):
        g.store(o, "sw")
    g.block(0x2D4A, 0x2D58)
    parts = [("w48", "(w44).toNat", "(.inl l_in)", f"(by rw [w{g.k}_424, ofNat_toNat_self])", "(by have := l_in.lo; omega)"),
             ("BitVec.ofNat 32 0x3FCC4850", "1", "(.inr ⟨by decide, by decide⟩)", f"w{g.k}_42c", "(by decide)"),
             ("BitVec.ofNat 32 0x3FCC47D7", "1", "(.inr ⟨by decide, by decide⟩)", f"w{g.k}_434", "(by decide)"),
             ("kp", "32", "(.inl kp_in)", f"w{g.k}_43c", "(by decide)")]
    g.parts4(0x2D58, 0x1380, 0x420, parts)
    g.digest_word()
    g.store(0x2D60, "sw")
    g.block(0x2D62, 0x2D6A)
    g.load(0x2D6A, "lw")
    g.store(0x2D6C, "sw")
    stmt, proof = finish(g, 0x2D6E, CL_KEEP_REGS, set(g.words), set(g.bytes))
    info = {"name": "sv_cs1", "title": "the log key's hash",
            "doc": "From the log's entry at 0x2D12 to the signature loop at 0x2D6E: the word at offset 0x14 is the "
            "first word of SHA-256 of the origin line, a newline, the Ed25519 key tag, and the log's key.",
            "params": params, "stmt": stmt, "proof": proof, "binders": CL_BINDERS.replace("op ol : Word}", "op ol kp kw : Word}"),
            "start": 0x2D12, "import": "C3BootProofs.Proofs.SvCkpt"}
    return g, info


CS_BINDERS = CL_BINDERS.replace("op ol : Word} {rt : Bytes}", "op ol : Word} {rt sg : Bytes}").replace(" w10 ", " ")
RK_BINDERS = CS_BINDERS.replace(" w70 ", " w70 w74 ")


def cs_start(g):
    """The signature loop's head at 0x2D6E: the word at 0x30 says whether a
    signature by the log was found, which would be at offsets 0x10 and 0x1480."""
    params = [q for q in cl_start(g) if not q.startswith("(w0_10 :")]
    g.words[0x10] = ("U", "(BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32")
    params.append(f"(w0_10 : memLoad32 n0.mem ({fa(0x10)}) = (BitVec.ofNat 8 (sg.getD 0 0)).zeroExtend 32)")
    g.ranges[0x1480] = (63, "BitVec.ofNat 8 (sg.getD (1 + j) 0)")
    params.append("(q0_1480 : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))")
    return params


def stage_csa():
    """From the signature loop's head at 0x2D6E to the name scan at 0x2DCC:
    the next line of the signature section starts with an em dash and a space."""
    g = Gen("Csa")
    g.generic_alu = True
    params = cs_start(g) + ["(hrem : w5c ≠ 0)", "(sg_in : SvIn B w38 w5c.toNat)", "(CK0 : SvCkCode M0)"]
    g.load(0x2D6E, "lw")
    g.block(0x2D70, 0x2D72)
    g.store(0x2D72, "sw")
    g.load(0x2D74, "lw")
    g.branch(0x2D76, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hrem")
    g.block(0x2D7A, 0x2D7E)
    g.load(0x2D7E, "lw")
    g.load(0x2D80, "lw")
    k, ix, rp, rn, rin = g.line(0x2D82, 0x420, "w38", "(w5c).toNat", "(.inl sg_in)",
                                f"(by rw [g{g.k}_12, ofNat_toNat_self])", ck_line_tail(0x2D8A, 22))
    g.load(0x2D8A, "lw")
    g.branch(0x2D8E, False, f"by rw [g{g.k}_22, s{g.k}.zero]; exact br_beq_f sg_in.pos_ne")
    g.load(0x2D92, "lw")
    g.block(0x2D96, 0x2D98)

    def short(sub):
        sub.branch(0x2D98, True, f"by rw [g{sub.k}_8, g{sub.k}_10]; exact br_bltu_t (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)")
        ck_fail_2ff2(sub, "h4")
    g.prop_check(f"4 ≤ {ix}", "h4", short)
    g.branch(0x2D98, False, f"by rw [g{g.k}_8, g{g.k}_10]; exact br_bltu_f (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)")
    g.pinned.add("h4")
    g.load(0x2D9C, "lw")
    g.store(0x2DA0, "sw")
    g.load(0x2DA2, "lw")
    g.store(0x2DA6, "sw")
    g.block(0x2DA8, 0x2DB4)
    ke = g.esl(0x2DB4, "w38", "BitVec.ofNat 32 0x3FCC4855", "4", f"(.inl (sg_in.shrink (by omega)))",
               "(.inr ⟨by decide, by decide⟩)")
    eq = "memBytes M0 w38 4 = memBytes M0 (BitVec.ofNat 32 0x3FCC4855) 4"

    def no_dash(sub):
        sub.set_a0(ke, 0, "ite_eq_right hdash")
        sub.branch(0x2DBC, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        ck_fail_2ff2(sub, "hdash")
    g.prop_check(eq, "hdash", no_dash)
    g.set_a0(ke, 1, "ite_eq_left hdash")
    g.branch(0x2DBC, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x2DC0, 0x2DC2)
    g.block(0x2DC2, 0x2DC6)
    g.block(0x2DC6, 0x2DC8)
    g.store(0x2DC8, "sw")
    g.store(0x2DCA, "sw")
    stmt, proof = finish(g, 0x2DCC, CL_KEEP_REGS + [8, 10], set(g.words), set(g.bytes))
    info = {"name": "sv_csa", "title": "a signature line's em dash",
            "doc": "From the signature loop's head at 0x2D6E to the name scan at 0x2DCC: the signature section isn't "
            "empty, and its next line has at least four bytes, an em dash and a space.",
            "params": params, "stmt": stmt, "proof": proof, "binders": CS_BINDERS, "start": 0x2D6E,
            "import": "C3BootProofs.Proofs.SvEd"}
    return g, info


def cn_start(g):
    params = cs_start(g)
    g.regs.update({9: ("U", "c"), 10: ("U", "pa"), 8: ("U", "nl0")})
    params += ["(g0_8 : reg n0 (8 : Fin 32) = nl0)", "(g0_10 : reg n0 a0 = pa)"]
    return params


def stage_cn(kind):
    """The name scan at 0x2DCC: a byte that isn't a space ("m", back to
    0x2DCC), the line's end ("e"), or the space ("s", on to the base64 groups
    at 0x2E0C)."""
    g = Gen("Cn" + kind)
    g.generic_alu = True
    params = cn_start(g)
    g.load(0x2DCC, "lw")
    if kind == "e":
        params.append("(heq : w40 = c)")

        def end(sub):
            sub.branch(0x2DCE, True, f"by rw [g{sub.k}_11, g{sub.k}_9]; exact br_beq_t heq")
            ck_fail_2ff2(sub, "hf")
        g.prop_check("False", "hf", end)
        stmt, _ = finish(g, 0x2DCC, [2], set(), set())
        g.emit("  exact hf.elim")
        proof = ""
        title, doc = "a signature line without a space", "The name scan at 0x2DCC reaches the line's end: `sigstore::verify` fails."
    else:
        params += ["(hne : w40 ≠ c)", "(pa_in : SvIn B pa 1)",
                   f"(hsp : M0 pa {'≠' if kind == 'm' else '='} 0x20)"]
        g.branch(0x2DCE, False, f"by rw [g{g.k}_11, g{g.k}_9]; exact br_beq_f hne")
        g.load_in(0x2DD2, "pa_in", "(by decide)")
        g.block(0x2DD6, 0x2DD8, {11: ("(M0 pa).zeroExtend 32 + 0xFFFFFFE0",
                                      "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, svCn" + kind + "2dd6, upd, ↓reduceIte]; rw [g{p}_11]; rfl")})
        if kind == "m":
            g.branch(0x2DD8, False, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_beq_f fun e => hsp ((space_iff _).mp e)")
            g.block(0x2DDA, 0x2DDC)
            g.block(0x2DDC, 0x2DDE)
            g.jump(0x2DDE)
            end, keep = 0x2DCC, CL_KEEP_REGS + [8, 10]
            title, doc = "a byte of a signature line's name", ("One pass of the name scan, from 0x2DCC back to it: "
                                                              "the next byte of the line isn't a space.")
        else:
            g.branch(0x2DD8, True, f"by rw [g{g.k}_11, s{g.k}.zero]; exact br_beq_t ((space_iff _).mpr hsp)")

            def empty(sub):
                sub.branch(0x2DE0, True, f"by rw [g{sub.k}_9, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not hc0)")
                ck_fail_2ff2(sub, "hc0")
            g.prop_check("c ≠ 0", "hc0", empty)
            g.branch(0x2DE0, False, f"by rw [g{g.k}_9, s{g.k}.zero]; exact br_beq_f hc0")
            g.block(0x2DE4, 0x2DE8)
            g.load(0x2DE8, "lw")
            g.block(0x2DEA, 0x2DEE)
            g.block(0x2DEE, 0x2DF2)
            r = lean_val(g.regs[10])

            def ragged(sub):
                sub.branch(0x2DF2, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t h4m")
                ck_fail_2ff2(sub, "h4m")
            g.prop_check(f"{r} = 0", "h4m", ragged)
            g.branch(0x2DF2, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f h4m")
            g.block(0x2DF6, 0x2DF8)
            g.block(0x2DF8, 0x2DFA)
            g.block(0x2DFA, 0x2DFE)
            g.load(0x2DFE, "lw")
            g.block(0x2E00, 0x2E02)
            g.store(0x2E02, "sw")
            g.block(0x2E04, 0x2E06)
            g.block(0x2E06, 0x2E08)
            g.store(0x2E08, "sw")
            g.block(0x2E0A, 0x2E0C)
            end, keep = 0x2E0C, CL_KEEP_REGS + [8, 10, 21, 22, 23]
            title, doc = "the space after a signature line's name", (
                "From the name scan at 0x2DCC to the base64 groups at 0x2E0C: the name isn't empty, and the base64 "
                "after the space has a multiple of four bytes.")
        stmt, proof = finish(g, end, sorted(set(keep)), set(g.words), set(g.bytes))
    info = {"name": "sv_cn" + kind, "title": title, "doc": doc,
            "params": params, "stmt": stmt, "proof": proof, "binders": CS_BINDERS.replace("op ol : Word}", "op ol c pa nl0 : Word}"),
            "start": 0x2DCC, "import": "C3BootProofs.Proofs.SvCs"}
    return g, info


def cg_start(g):
    params = cs_start(g)
    new = {10: "pg", 22: "gi", 8: "s0v", 21: "s5v", 23: "s7v"}
    params = [q for q in params if not any(q.startswith(f"(g0_{r} :") for r in new)]
    for r, v in new.items():
        g.regs[r] = ("U", v)
        params.append(f"(g0_{r} : reg n0 {rname(r)} = {v})")
    return params


def stage_cg(kpad):
    """One pass of the base64 group loop, from 0x2E0C back to it, for a group
    whose first `=` is at position `kpad` (4: none): the group decodes."""
    g = Gen(f"Cg{kpad}")
    g.generic_alu = True
    params = cg_start(g)
    params += ["(hne : pg ≠ w8)", "(CK0 : SvCkCode M0)", "(pg_in : SvIn B pg 4)",
               "(pb1 : SvIn B (pg + 0x1) 1)", "(pb2 : SvIn B (pg + 0x2) 1)", "(pb3 : SvIn B (pg + 0x3) 1)"]
    g.load(0x2E0C, "lw")
    g.branch(0x2E0E, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_beq_f hne")
    g.load_in(0x2E12, "pb1", "(by decide)")
    g.load_in(0x2E16, "pb2", "(by decide)")
    g.load_in(0x2E1A, "pb3", "(by decide)")
    g.load_in(0x2E1E, "pg_in", "(by decide)")
    for o, e in ((0x2E22, 0x2E24), (0x2E24, 0x2E26), (0x2E26, 0x2E28), (0x2E28, 0x2E2A), (0x2E2A, 0x2E2C), (0x2E2C, 0x2E2E)):
        g.block(o, e)
    k = g.k
    g.emit(f"  have pk{k} : {lean_val(g.regs[11])} = memLoad32 M0 pg := pack4 _ _ _ _")
    g.emit(f"  rw [pk{k}] at g{k}_11")
    g.regs[11] = ("U", "memLoad32 M0 pg")
    g.block(0x2E2E, 0x2E32)
    g.block(0x2E32, 0x2E3A)
    g.store(0x2E3A, "sw")
    g.block(0x2E3C, 0x2E3E)
    g.block(0x2E3E, 0x2E40)
    for j in range(4):
        if j == kpad:
            break
        g.branch(0x2E40, False, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
        addr = lean_val(g.regs[10])
        nm = f"pc{j}"
        params.append(f"({nm} : SvIn B ({addr}) 1)")
        g.load_in(0x2E42, nm, "(by decide)")
        g.block(0x2E46, 0x2E4A, {12: (f"(M0 ({addr})).zeroExtend 32 + 0xFFFFFFC3",
                                      "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, " + f"svCg{kpad}2e46" + ", upd, ↓reduceIte]; rw [g{p}_12]; rfl")})
        g.block(0x2E4A, 0x2E4C)
        g.block(0x2E4C, 0x2E4E)
        hn = f"hq{j}"
        params.append(f"({hn} : M0 ({addr}) ≠ 0x3D)")
        g.branch(0x2E4E, True, f"by rw [g{g.k}_12, s{g.k}.zero]; exact br_bne_t fun e => {hn} ((pad_iff _).mp e)")
    if kpad < 4:
        g.branch(0x2E40, False, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
        addr = lean_val(g.regs[10])
        params.append(f"(pc{kpad} : SvIn B ({addr}) 1)")
        params.append(f"(hq{kpad} : M0 ({addr}) = 0x3D)")
        g.load_in(0x2E42, f"pc{kpad}", "(by decide)")
        g.block(0x2E46, 0x2E4A, {12: (f"(M0 ({addr})).zeroExtend 32 + 0xFFFFFFC3",
                                      "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, " + f"svCg{kpad}2e46" + ", upd, ↓reduceIte]; rw [g{p}_12]; rfl")})
        g.block(0x2E4A, 0x2E4C)
        g.block(0x2E4C, 0x2E4E)
        g.branch(0x2E4E, False, f"by rw [g{g.k}_12, s{g.k}.zero]; exact br_bne_f ((pad_iff _).mpr hq{kpad})")
        g.load(0x2E50, "lw")
        last = lean_val(g.regs[22])

        def not_last(sub):
            sub.branch(0x2E52, True, f"by rw [g{sub.k}_22, g{sub.k}_10]; exact br_bne_t hlast")
            ck_fail_2ff2(sub, "hlast")
        g.prop_check(f"{last} = {lean_val(g.words[0xC])}", "hlast", not_last)
        g.branch(0x2E52, False, f"by rw [g{g.k}_22, g{g.k}_10]; exact br_bne_f hlast")
    else:
        g.branch(0x2E40, True, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
    g.block(0x2E56, 0x2E68)
    kb = g.b64f(0x2E68, 0x420, 0x200, 0x1380, "4", "3")
    g.emit(f"  rw [mb4_of_ld w{kb-1}_1380] at Ok{kb} Bad{kb}")
    ex = "base64Decode (memBytes M0 pg 4)"
    g.emit(f"  obtain ⟨r{kb}, hr{kb}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rcases r{kb} with _ | bq{kb}")
    g.sc.append(("eq", ex, f"some bq{kb}", [f"bq{kb}"], f"hr{kb}"))

    def bad_tail(sub):
        sub.load(0x2E70, "lbu")
        sub.block(0x2E74, 0x2E76)
        sub.branch(0x2E76, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; decide")

    def none(sub):
        sub.emit(f"  have z{kb} := Bad{kb} fun b h => by rw [hr{kb}] at h; cases h")
        sub.frame_after(kb, [(0x420, 8), (0x200, 3)], {}, {0x420: ("(1 : BitVec 8)", f"z{kb}")})
        bad_tail(sub)
        ck_fail_none(sub, ("eq", f"hr{kb}"))
    g.fork(none)

    def long(sub):
        sub.emit(f"  have z{kb} := Bad{kb} fun b h => by rw [hr{kb}] at h; cases h; omega")
        sub.frame_after(kb, [(0x420, 8), (0x200, 3)], {}, {0x420: ("(1 : BitVec 8)", f"z{kb}")})
        bad_tail(sub)
        ck_fail_none(sub, ("prop", "hl3"))
    g.prop_check(f"bq{kb}.length ≤ 3", "hl3", long)
    g.emit(f"  have z{kb} := Ok{kb} bq{kb} hr{kb} hl3")
    g.frame_after(kb, [(0x420, 8), (0x200, 3)], {}, {0x420: ("(0 : BitVec 8)", f"z{kb}")})
    g.load(0x2E70, "lbu")
    g.block(0x2E74, 0x2E76)
    g.branch(0x2E76, False, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
    g.jump(0x2E7A)
    keep = sorted(set(CL_KEEP_REGS + [8, 10, 21, 22, 23, 24]))
    stmt, proof = finish(g, 0x2E0C, keep, set(g.words) - {0x420, 0x424}, set())
    info = {"name": f"sv_cg{kpad}", "title": "a base64 group of a signature line",
            "doc": f"One pass of the base64 group loop, from 0x2E0C back to it: the next four bytes decode as base64, "
            + ("and none is `=`." if kpad == 4 else f"their first `=` is byte {kpad}, and this is the last group."),
            "params": params, "stmt": stmt, "proof": proof,
            "binders": CS_BINDERS.replace("op ol : Word}", "op ol pg gi s0v s5v s7v : Word}"),
            "start": 0x2E0C, "import": "C3BootProofs.Proofs.SvCs"}
    return g, info


CM_DOC = {
    "n": "the line names another log, and the loop moves to the next line.",
    "dn": "the line names the log, and its base64 doesn't decode: `sigstore::verify` fails.",
    "dl": "the line names the log, and its signature decodes to more than 96 bytes: `sigstore::verify` fails.",
    "s": "the line names the log, and its signature decodes to fewer than four bytes: the loop moves to the next line.",
    "k": "the line names the log, and its key ID isn't the log's: the loop moves to the next line.",
    "x": "the line names the log with the log's key ID, and its signature isn't 68 bytes: `sigstore::verify` fails.",
    "f": "the line names the log with the log's key ID and a 68-byte signature, which goes to offsets 0x10 and 0x1480 "
         "if no other line did.",
}


def stage_cm(kind):
    """From the base64 group loop's end at 0x2E0C: the name against the
    checkpoint's origin, then the signature."""
    g = Gen("Cm" + kind)
    g.generic_alu = True
    params = cg_start(g)
    params = [q for q in params if not q.startswith("(g0_9 :")]
    params.append("(g0_9 : reg n0 (9 : Fin 32) = c)")
    params += ["(hend : pg = w8)", "(hnz : w40 ≠ s5v)", "(nm_in : SvIn B w28 c.toNat)", "(l_in : SvIn B w48 w44.toNat)"]
    eqn = "memBytes M0 w28 c.toNat = memBytes M0 w48 w44.toNat"
    params.append(f"(hnm : {'¬ ' if kind == 'n' else ''}{eqn})")
    dec = "base64Decode (memBytes M0 s7v s0v.toNat)"
    if kind != "n":
        params += ["(CK0 : SvCkCode M0)", "(b_in : SvIn B s7v s0v.toNat)"]
    if kind == "dn":
        params.append(f"(hdec : {dec} = none)")
    elif kind not in ("n",):
        params.append(f"(hdec : {dec} = some bs)")
    if kind == "dl":
        params.append("(hbig : 0x60 < bs.length)")
    elif kind in ("s", "k", "x", "f"):
        params.append("(hle : bs.length ≤ 0x60)")
    if kind == "s":
        params.append("(hsh : bs.length < 4)")
    if kind in ("k", "x", "f"):
        params.append("(h4 : 4 ≤ bs.length)")
        params.append(f"(hk : le4 bs 0 {'≠' if kind == 'k' else '='} w14)")
    if kind == "x":
        params.append("(h68 : bs.length ≠ 68)")
    if kind == "f":
        params.append("(h68 : bs.length = 68)")
    fails = kind in ("dn", "dl", "x")
    g.load(0x2E0C, "lw")
    g.branch(0x2E0E, True, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_beq_t hend")
    g.load(0x2E7C, "lw")
    g.branch(0x2E7E, False, f"by rw [g{g.k}_10, g{g.k}_21]; exact br_beq_f hnz")
    g.load(0x2E82, "lw")
    g.block(0x2E84, 0x2E86)
    g.load(0x2E86, "lw")
    g.load(0x2E88, "lw")
    ks = g.sne(0x2E8A, "w28", "c.toNat", "w48", "w44.toNat", "(.inl nm_in)", "(.inl l_in)",
               f"(by rw [g{g.k}_11, ofNat_toNat_self])", f"(by rw [g{g.k}_13, ofNat_toNat_self])")

    def body(g):
        if kind == "n":
            g.set_a0(ks, 1, "ite_eq_right hnm")
            g.branch(0x2E92, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            return 0x2D6E
        g.set_a0(ks, 0, "ite_eq_left hnm")
        g.branch(0x2E92, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        g.block(0x2E96, 0x2EA0)
        g.ms(0x2EA0, 0x420, 0x60)
        g.block(0x2EA8, 0x2EBC)
        kb, ex = g.b64(0x2EBC, 0x1380, 0x420, "s7v", "(s0v).toNat", "(.inl b_in)",
                       f"(by rw [g{g.k}_12, ofNat_toNat_self])", "0x60")
        if kind in ("dn", "dl"):
            if kind == "dn":
                g.emit(f"  have z{kb} := Bad{kb} fun b h => by rw [hdec] at h; cases h")
            else:
                g.emit(f"  have z{kb} := Bad{kb} fun b h => by rw [hdec] at h; cases h; exact hbig")
            g.frame_after(kb, [(0x1380, 8), (0x420, 0x60)], {}, {0x1380: ("(1 : BitVec 8)", f"z{kb}")})
            g.block(0x2EC4, 0x2ECC)
            g.load(0x2ECC, "lbu")
            g.branch(0x2ED0, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
            return None
        g.emit(f"  obtain ⟨b0_{kb}, b4_{kb}, bm_{kb}⟩ := Ok{kb} bs hdec hle")
        g.pinned |= {f"bm_{kb}"}
        g.frame_after(kb, [(0x1380, 8), (0x420, 0x60)], {0x1384: ("BitVec.ofNat 32 bs.length", f"b4_{kb}")},
                      {0x1380: ("(0 : BitVec 8)", f"b0_{kb}")})
        if kind in ("k", "x", "f"):
            g.words[0x420] = ("U", "le4 bs 0")
            g.emit(f"  have w{kb}_420 : {g.word_stmt(kb, 0x420, ('U', 'le4 bs 0'))} := ld_digest bm_{kb} h4")
        if kind == "f":
            g.ranges[0x420] = (68, "BitVec.ofNat 8 (bs.getD j 0)")
            g.emit(f"  have q{kb}_420 : ∀ j, j < 68 → n{kb}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs.getD j 0) :=")
            g.emit(f"    fun j hj => by rw [← add_ofNat_assoc]; exact memBytes_range bm_{kb} j (by omega)")
        g.block(0x2EC4, 0x2ECC)
        g.load(0x2ECC, "lbu")
        g.branch(0x2ED0, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        g.block(0x2ED4, 0x2EDC)
        g.load(0x2EDC, "lw")
        g.block(0x2EDE, 0x2EE2)
        g.branch(0x2EE2, False, f"by rw [g{g.k}_11, g{g.k}_10]; exact br_bltu_f (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)")
        g.block(0x2EE6, 0x2EE8)
        if kind == "s":
            g.branch(0x2EE8, True, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bltu_t (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)")
            return 0x2D6E
        g.branch(0x2EE8, False, f"by rw [g{g.k}_10, g{g.k}_11]; exact br_bltu_f (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)")
        g.load(0x2EEC, "lw")
        g.load(0x2EF0, "lw")
        if kind == "k":
            g.branch(0x2EF2, True, f"by rw [g{g.k}_11, g{g.k}_12]; exact br_bne_t hk")
            return 0x2D6E
        g.branch(0x2EF2, False, f"by rw [g{g.k}_11, g{g.k}_12]; exact br_bne_f hk")
        g.block(0x2EF6, 0x2EFA)
        if kind == "x":
            g.branch(0x2EFA, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_t (ne68_add (by omega) h68)")
            return None
        g.branch(0x2EFA, False, f"by rw [g{g.k}_10, s{g.k}.zero, h68]; decide")
        g.load(0x2EFC, "lbu")
        g.store(0x2F00, "sw")
        g.block(0x2F02, 0x2F12)
        g.mc(0x2F12, 0x1480, 0x425, 0x3F)
        g.load(0x2F1A, "lw")
        dup = lean_val(g.regs[10])

        def again(sub):
            sub.branch(0x2F1C, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_bne_t hdup")
            ck_fail_2ff2(sub, "hdup")
        g.prop_check(f"{dup} = 0", "hdup", again)
        g.branch(0x2F1C, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_f hdup")
        g.block(0x2F1E, 0x2F20)
        g.store(0x2F20, "sw")
        g.jump(0x2F22)
        return 0x2D6E

    if fails:
        def fail_all(sub):
            body(sub)
            ck_fail_2ff2(sub, "hf")
        g.prop_check("False", "hf", fail_all)
        stmt, _ = finish(g, 0x2D6E, [2], set(), set())
        g.emit("  exact hf.elim")
        proof = ""
    else:
        end = body(g)
        keep = sorted(set(CL_KEEP_REGS))
        stmt, proof = finish(g, end, keep, set(g.words) - {0x420, 0x424, 0x428, 0x42C}, set())
    info = {"name": "sv_cm" + kind, "title": "a signature line's name and signature",
            "doc": "From the base64 group loop's end at 0x2E0C: " + CM_DOC[kind],
            "params": params, "stmt": stmt, "proof": proof,
            "binders": CS_BINDERS.replace("op ol : Word}", "op ol pg gi s0v s5v s7v : Word}").replace("{rt sg : Bytes}", "{rt sg bs : Bytes}"),
            "start": 0x2E0C, "import": "C3BootProofs.Proofs.SvCs"}
    return g, info


def stage_csx():
    """From the signature loop's head at 0x2D6E, with no lines left, to 0x2F5A:
    a line signed the checkpoint with the log's key."""
    g = Gen("Csx")
    g.generic_alu = True
    params = cs_start(g) + ["(hrem0 : w5c = 0)", "(EE0 : EvEnv M0)", "(RS : SvRoSep B)",
                            "(hiv : (s5Hv M0 (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0)",
                            "(pk_in : SvIn B w34 32)", "(msg_in : SvIn B w24 w20.toNat)", "(hlen : w20.toNat < 2 ^ 31)"]
    g.load(0x2D6E, "lw")
    g.block(0x2D70, 0x2D72)
    g.store(0x2D72, "sw")
    g.load(0x2D74, "lw")
    g.branch(0x2D76, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hrem0")
    g.load(0x2F24, "lw")
    fl = lean_val(g.regs[10])

    def none(sub):
        sub.branch(0x2F26, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not hfound)")
        sub.block(0x2FF8, 0x2FFA)
        sub.jump(0x2FFA)
        sub.fail(sub.fail_proof(("prop", "hfound")))
    g.prop_check(f"{fl} ≠ 0", "hfound", none)
    g.branch(0x2F26, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hfound")
    g.block(0x2F28, 0x2F38)
    g.mc(0x2F38, 0x421, 0x1480, 0x3F)
    g.load(0x2F40, "lw")
    g.store(0x2F42, "sb")
    g.block(0x2F46, 0x2F4A)
    g.load(0x2F4A, "lw")
    g.load(0x2F4C, "lw")
    g.load(0x2F4E, "lw")
    k = g.k
    g.pinned.add(f"hs{k}")
    g.emit(f"  have hs{k} := sig_join b{k}_420 q{k}_421")
    ke = g.ed(0x2F50, 0x420, "w34", "w24", "(w20).toNat", "sg", f"hs{k}", "pk_in", "msg_in", "hlen",
              f"(by rw [g{g.k}_12, ofNat_toNat_self])")
    ev = "evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg) w34 (B + 0x21A0 + BitVec.ofNat 32 0x420) w24 (w20).toNat = true"

    def bad(sub):
        sub.set_a0(ke, 0, "ite_eq_right hev")
        sub.branch(0x2F58, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.block(0x2FFE, 0x3000)
        sub.jump(0x3000)
        sub.fail(sub.fail_proof(("prop", "hev")))
    g.prop_check(ev, "hev", bad)
    g.set_a0(ke, 1, "ite_eq_left hev")
    g.branch(0x2F58, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0x2F5A, sorted(set(CL_KEEP_REGS)), set(g.words), set())
    info = {"name": "sv_csx", "title": "the checkpoint's signature",
            "doc": "From the signature loop's head at 0x2D6E, with nothing left, to 0x2F5A: a line signed by the log "
            "was found, and `ed25519_verify` accepts its signature over the checkpoint's body with the log's key.",
            "params": params, "stmt": stmt, "proof": proof, "binders": CS_BINDERS, "start": 0x2D6E,
            "import": "C3BootProofs.Proofs.SvCs"}
    return g, info


def stage_cr1(eqhi):
    """From the checkpoint's signature at 0x2F5A to 0x300E: the checkpoint's
    fields go to offset 0x1020, and the entry's index is below the size."""
    g = Gen("Cr1" + ("e" if eqhi else "n"))
    g.generic_alu = True
    params = cs_start(g)
    params += ["(lid_in : SvIn B (q + BitVec.ofNat 32 0x5) 19)", "(h80 : w80 ≠ 0)",
               "(hlih : memLoad32 M0 (bp + 0x2C) = lih)", "(hlil : memLoad32 M0 (bp + 0x28) = lil)",
               "(lih_in : SvIn B (bp + 0x2C) 4)", "(lil_in : SvIn B (bp + 0x28) 4)",
               "(a_lih : (bp + 0x2C).toNat % 4 = 0)", "(a_lil : (bp + 0x28).toNat % 4 = 0)",
               f"(hhi : lih {'=' if eqhi else '≠'} w70)"]
    g.block(0x2F5A, 0x2F62)
    g.mcIn(0x2F62, 0x240, lean_val(g.regs[11]), 0x13, "lid_in")
    g.block(0x2F6A, 0x2F76)
    g.mc(0x2F76, 0x1320, 0x320, 0x1F)
    g.load(0x2F7E, "lw")
    g.branch(0x2F80, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_bne_t h80")
    g.block(0x2F86, 0x2F92)
    g.mc(0x2F92, 0x1025, 0x240, 0x13)
    g.load(0x2F9A, "lw")
    g.block(0x2F9C, 0x2FA0)
    g.store(0x2FA0, "sw")
    g.load(0x2FA2, "lw")
    g.store(0x2FA4, "sw")
    g.load(0x2FA6, "lw")
    g.store(0x2FA8, "sb")
    g.block(0x2FAC, 0x2FBE)
    g.mc(0x2FBE, 0x1049, 0x1320, 0x1F)
    g.load_mem(0x2FC6, "lih", "hlih", "lih_in", "a_lih")
    g.load_mem(0x2FCA, "lil", "hlil", "lil_in", "a_lil")
    g.load(0x2FCE, "lw")
    g.store(0x2FD0, "sw")
    g.store(0x2FD2, "sb")
    g.load(0x2FD6, "lw")
    g.store(0x2FD8, "sw")
    g.load(0x2FDA, "lw")
    g.store(0x2FDC, "sw")
    if eqhi:
        g.branch(0x2FDE, True, f"by rw [g{g.k}_23, g{g.k}_10]; exact br_beq_t hhi")
        g.load(0x3004, "lw")
        g.block(0x3006, 0x300A)
    else:
        g.branch(0x2FDE, False, f"by rw [g{g.k}_23, g{g.k}_10]; exact br_beq_f hhi")
        g.load(0x2FE2, "lw")
        g.block(0x2FE4, 0x2FE8)
        g.jump(0x2FE8)
    lt = lean_val(g.regs[10])

    def big(sub):
        sub.branch(0x300A, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_t (Decidable.of_not_not hidx)")
        sub.fail(sub.fail_proof(("prop", "hidx")), "sv_fail_3122")
    g.prop_check(f"{lt} ≠ 0", "hidx", big)
    g.branch(0x300A, False, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_f hidx")
    stmt, proof = finish(g, 0x300E, sorted(set(CL_KEEP_REGS + [8, 23])), set(g.words), set(g.bytes))
    info = {"name": "sv_cr1" + ("e" if eqhi else "n"), "title": "the entry's index against the checkpoint's size",
            "doc": "From the checkpoint's signature at 0x2F5A to 0x300E: the checkpoint's log, size, and root go to "
            "offset 0x1020, and the entry's 64-bit index is below the size.",
            "params": params, "stmt": stmt, "proof": proof, "binders": CS_BINDERS.replace("op ol : Word}", "op ol lih lil : Word}"),
            "start": 0x2F5A, "import": "C3BootProofs.Proofs.SvRk"}
    return g, info


def rk_start(g):
    """After the entry's index check at 0x300E: `s7` and `s9` hold the index,
    `s0` the checkpoint's fields at offset 0x1020, whose root is at 0x1048."""
    params = cs_start(g)
    params = [q for q in params if not (q.startswith("(g0_23 :") or q.startswith("(g0_25 :"))]
    g.regs[23] = ("U", "lih")
    g.regs[25] = ("U", "lil")
    g.regs[8] = ("S", 0x1020)
    g.words[0x74] = ("U", "w74")
    params.append(f"(w0_74 : memLoad32 n0.mem ({fa(0x74)}) = w74)")
    rb = "((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8"
    g.bytes[0x1048] = rb
    g.ranges[0x1049] = (31, "BitVec.ofNat 8 (rt.getD (1 + j) 0)")
    params += ["(g0_23 : reg n0 (23 : Fin 32) = lih)", "(g0_25 : reg n0 (25 : Fin 32) = lil)",
               "(g0_8 : reg n0 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1020)",
               f"(b0_1048 : n0.mem ({fa(0x1048)}) = {rb})",
               "(q0_1049 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1049 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))",
               "(S2 : SvSha2Code M0)", "(KS : SvK2Sep B)", "(RS : SvRoSep B)", "(RK0 : SvRkCode M0)"]
    return params


def stage_rl():
    """From 0x300E to 0x30EC: the log entry's leaf hash."""
    g = Gen("Rl")
    g.generic_alu = True
    params = rk_start(g)
    params += ["(dgi_in : SvIn B w84 32)", "(sig_in : SvIn B w68 w64.toNat)", "(crt_in : SvIn B w6c x26.toNat)"]
    ro = "(Or.inr ⟨by decide, by decide⟩)"
    g.store(0x300E, "sb")
    g.block(0x3012, 0x3022)
    g.mcRo(0x3022, 0x460, "BitVec.ofNat 32 0x3FCC42A8", 0x20, ro)
    g.store(0x302A, "sw")
    g.store(0x302E, "sw")
    g.hinit()
    g.block(0x3032, 0x3040)
    g.upd(0x3040, "BitVec.ofNat 32 0x3FCC4106", "0x1", ro, "(by decide)", "")
    g.block(0x3048, 0x3058)
    g.upd(0x3058, "BitVec.ofNat 32 0x3FCC46F0", "0x71", ro, "(by decide)", "")
    g.block(0x3060, 0x3068)
    g.carry_hasher()
    g.load(0x3068, "lw")
    g.b64e(0x306A, "w84", "32", "(.inl dgi_in)", f"g{g.k}_11", "")
    g.block(0x3072, 0x3082)
    g.upd(0x3082, "BitVec.ofNat 32 0x3FCC4761", "0x1B", ro, "(by decide)", "")
    g.block(0x308A, 0x308E)
    g.carry_hasher()
    g.load(0x308E, "lw")
    g.carry_hasher()
    g.load(0x3090, "lw")
    g.b64e(0x3092, "w68", "(w64).toNat", "(.inl sig_in)", f"(by rw [g{g.k}_11, ofNat_toNat_self])", "have := sig_in.lo")
    g.block(0x309A, 0x30AA)
    g.upd(0x30AA, "BitVec.ofNat 32 0x3FCC477C", "0x54", ro, "(by decide)", "have := sig_in.lo")
    g.block(0x30B2, 0x30B6)
    g.carry_hasher()
    g.load(0x30B6, "lw")
    g.carry_hasher()
    g.block(0x30B8, 0x30BA)
    g.b64e(0x30BA, "w6c", "(x26).toNat", "(.inl crt_in)", f"(by rw [g{g.k}_11, ofNat_toNat_self])",
           "have := sig_in.lo; have := crt_in.lo")
    g.block(0x30C2, 0x30D0)
    g.upd(0x30D0, "BitVec.ofNat 32 0x3FCC47D0", "0x7", ro, "(by decide)", "have := sig_in.lo; have := crt_in.lo")
    g.block(0x30D8, 0x30E4)
    g.fin(0x30E4, 0x1380)
    kd, oc, ex = g.digest
    g.extra.append((f"memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x{oc:X}) 32 = {ex}", f"D{kd}"))
    stmt, proof = finish(g, 0x30EC, sorted(set(CL_KEEP_REGS + [8, 23])), set(g.words) - {0x480, 0x484})
    info = {"name": "sv_rl", "title": "the log entry's leaf hash",
            "doc": "From 0x300E to 0x30EC: SHA-256 of the entry's canonical body, built from its constant parts and "
            "the base64 of the image digest, the image signature, and the leaf certificate, goes to offset 0x1380.",
            "params": params, "stmt": stmt, "proof": proof, "binders": RK_BINDERS.replace("op ol : Word}", "op ol lih lil : Word}"),
            "start": 0x300E, "import": "C3BootProofs.Proofs.SvRk"}
    return g, info


def stage_rm():
    """From 0x30EC to 0x316E: the inclusion proof's root is the checkpoint's."""
    g = Gen("Rm")
    g.generic_alu = True
    params = rk_start(g)
    g.digest = (0, 0x1380, "lh")
    g.pinned.add("D0")
    params += ["(D0 : memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) 32 = lh)",
               "(hpp : memLoad32 M0 (bp + 0x10) = pp)", "(hpl : memLoad32 M0 (bp + 0x14) = pl)",
               "(pp_in4 : SvIn B (bp + 0x10) 4)", "(pl_in4 : SvIn B (bp + 0x14) 4)",
               "(a_pp : (bp + 0x10).toNat % 4 = 0)", "(a_pl : (bp + 0x14).toNat % 4 = 0)",
               "(pp_in : SvIn B pp pl.toNat)"]
    g.load_mem(0x30EC, "pp", "hpp", "pp_in4", "a_pp")
    g.carry_digest()
    g.load_mem(0x30F0, "pl", "hpl", "pl_in4", "a_pl")
    g.carry_digest()
    g.block(0x30F4, 0x3106)
    g.carry_digest()
    g.load(0x3106, "lw")
    g.carry_digest()
    g.load(0x3108, "lw")
    g.carry_digest()
    k, ex = g.rfi(0x310A, "pp", "(pl).toNat", "(Or.inl pp_in)", f"(by rw [g{g.k}_17, ofNat_toNat_self])")
    g.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {ex} = r := ⟨_, rfl⟩")
    g.emit(f"  rw [hr{k}] at R{k}")
    g.emit(f"  rcases r{k} with _ | root{k}")
    g.sc.append(("eq", ex, f"some root{k}", [f"root{k}"], f"hr{k}"))

    def none(sub):
        sub.emit(f"  obtain ⟨z{k}, y{k}⟩ := R{k}")
        sub.frame_after(k, [(0x420, 33)], {}, {0x420: ("(1 : BitVec 8)", f"z{k}"), 0x421: ("(0x1B : BitVec 8)", f"y{k}")})
        sub.load(0x3112, "lbu")
        sub.load(0x3116, "lbu")
        sub.branch(0x311A, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.block(0x311C, 0x311E)
        sub.jump(0x311E)
        sub.fail(sub.fail_proof(("eq", f"hr{k}")))
    g.fork(none)
    g.emit(f"  obtain ⟨z{k}, rb{k}⟩ := R{k}")
    g.pinned.add(f"rb{k}")
    g.frame_after(k, [(0x420, 33)], {}, {0x420: ("(0 : BitVec 8)", f"z{k}")})
    g.ranges[0x421] = (32, f"BitVec.ofNat 8 (root{k}.getD j 0)")
    g.emit(f"  have q{k}_421 : ∀ j, j < 32 → n{k}.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (root{k}.getD j 0) :=")
    g.emit(f"    fun j hj => by rw [← add_ofNat_assoc]; exact memBytes_range rb{k} j hj")
    g.load(0x3112, "lbu")
    g.load(0x3116, "lbu")
    g.branch(0x311A, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x312A, 0x3134)
    g.block(0x3134, 0x3142)
    g.mc(0x3142, 0x1481, 0x422, 0x1F)
    g.block(0x314A, 0x3152)
    g.store(0x3152, "sb")
    g.block(0x3156, 0x3160)
    ke = g.a32eq(0x3160, 0x1480, 0x1048, lambda k: [
        f"  rw [join32 b{k-1}_1480 q{k-1}_1481, join32 (b{k-1}_1048.trans (zext_lo8 _)) q{k-1}_1049] at a0_{k}"])
    eq = f"b32 root{k} = b32 rt"

    def differ(sub):
        sub.set_a0(ke, 0, "ite_eq_right hroot")
        sub.branch(0x3168, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.jump(0x316A)
        sub.fail(sub.fail_proof(("prop", "hroot")))
    g.prop_check(eq, "hroot", differ)
    g.set_a0(ke, 1, "ite_eq_left hroot")
    g.branch(0x3168, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0x316E, sorted(set(CL_KEEP_REGS + [8, 23])), set(g.words) - {0x420, 0x424, 0x428, 0x42C})
    info = {"name": "sv_rm", "title": "the inclusion proof",
            "doc": "From 0x30EC to 0x316E: `root_from_inclusion` rebuilds a root from the leaf hash at offset 0x1380, the "
            "entry's index, the checkpoint's size, and the bundle's proof, and the root is the checkpoint's.",
            "params": params, "stmt": stmt, "proof": proof,
            "binders": RK_BINDERS.replace("op ol : Word}", "op ol lih lil pp pl : Word}").replace("{rt sg : Bytes}", "{rt sg lh : Bytes}"),
            "start": 0x30EC, "import": "C3BootProofs.Proofs.SvRk"}
    return g, info


# The validity-window checks after 0x316E. Each compares the timestamp's
# 64-bit time (words 0x3C and 0x78) with one bound, high words first. For
# each: its first offset, whether `beq` puts the bound first, the loads on
# the equal and unequal paths, `sltu`'s offset, whether it computes
# time < bound (else bound < time), the `beqz` and its target, and the
# `j 0x966` it skips.
WIN = [
    # (start, hi loads, beq, eq target, eq loads, ne loads, ne jump, sltu, time_lt_bound, extra, beqz, next, fail_j)
    (0x316E, [(0x316E, "lw"), (0x3170, "lw")], (0x3172, "a0a1"), 0x317C, [(0x317C, "lw"), (0x317E, "lw")],
     [(0x3176, "lw"), (0x3178, "lw")], 0x317A, 0x3180, True, [(0x3184, 0x3186)], 0x3186, 0x318C, 0x3188),
    (0x318C, [(0x318C, "lw"), (0x318E, "lw")], (0x3190, "a1a0"), 0x319A, [(0x319A, "lw"), (0x319C, "lw")],
     [(0x3194, "lw"), (0x3196, "lw")], 0x3198, 0x319E, False, [], 0x31A2, 0x31A8, 0x31A4),
    (0x31A8, [(0x31A8, "lw"), (0x31AA, "mem:i2h"), (0x31AE, "lw")], (0x31B0, "a0a1"), 0x31B8,
     [(0x31B8, "lw"), (0x31BA, "mem:i2l"), (0x31BE, "lw")], [(0x31B4, "lw")], 0x31B6, 0x31C0, True, [], 0x31C4, 0x31CA, 0x31C6),
    (0x31CA, [(0x31CA, "lw"), (0x31CC, "mem:i3h"), (0x31D0, "lw")], (0x31D2, "a1a0"), 0x31DA,
     [(0x31DA, "lw"), (0x31DC, "mem:i3l"), (0x31E0, "lw")], [(0x31D6, "lw")], 0x31D8, 0x31E2, False, [], 0x31E6, 0x31EC, 0x31E8),
    (0x31EC, [(0x31EC, "lw"), (0x31EE, "mem:t4h"), (0x31F0, "lw")], (0x31F2, "a0a1"), 0x31FA,
     [(0x31FA, "lw"), (0x31FC, "mem:t4l"), (0x31FE, "lw")], [(0x31F6, "lw")], 0x31F8, 0x3200, True, [], 0x3204, 0x320A, 0x3206),
    (0x320A, [(0x320A, "lw"), (0x320C, "mem:t5h"), (0x320E, "lw")], (0x3210, "a1a0"), 0x3218,
     [(0x3218, "lw"), (0x321A, "mem:t5l"), (0x321C, "lw")], [(0x3214, "lw")], 0x3216, 0x321E, False, [], 0x3222, 0x3228, 0x3224),
    (0x3228, [(0x3228, "lw"), (0x322C, "lw")], (0x322E, "a0a1"), 0x3236, [(0x3236, "lw"), (0x323A, "lw")],
     [(0x3232, "lw")], 0x3234, 0x323C, True, [], 0x3240, 0x3246, 0x3242),
    (0x3246, [(0x3246, "lw"), (0x324A, "lw")], (0x324C, "a1a0"), 0x3254, [(0x3254, "lw"), (0x3258, "lw")],
     [(0x3250, "lw")], 0x3252, 0x325A, False, [], 0x325E, 0x3264, 0x3260),
]

# The words outside the stack that the intermediate and TSA windows load:
# name -> (base word, offset as the instruction writes it).
WIN_MEM = {"i2h": ("w7c", "0xFFFFFFE8"), "i2l": ("w7c", "0xFFFFFFE4"), "i3h": ("w7c", "0xFFFFFFF0"),
           "i3l": ("w7c", "0xFFFFFFEC"), "t4h": ("w74", "0xC"), "t4l": ("w74", "0x8"),
           "t5h": ("w74", "0x14"), "t5l": ("w74", "0x10")}


def stage_win(i, eq):
    """Validity-window check `i`, with the time's high word equal to the
    bound's (`eq`) or not."""
    (st, hi, (beq, order), eqt, eql, nel, nej, sl, tlb, extra, bz, nxt, fj) = WIN[i]
    g = Gen(f"Win{i}{'e' if eq else 'n'}")
    g.generic_alu = True
    params = rk_start(g)
    for e, nm in ((0x1028, "k28"), (0x102C, "k2c"), (0x1030, "k30"), (0x1034, "k34")):
        g.words[e] = ("U", nm)
        params.append(f"(w0_{e:x} : memLoad32 n0.mem ({fa(e)}) = {nm})")

    def loads(lst):
        for o, kind in lst:
            if kind.startswith("mem:"):
                nm = kind[4:]
                base, imm = WIN_MEM[nm]
                params.extend([f"(h{nm} : memLoad32 M0 ({base} + {imm}) = {nm})", f"(i{nm} : SvIn B ({base} + {imm}) 4)",
                               f"(a{nm} : ({base} + {imm}).toNat % 4 = 0)"])
                g.load_mem(o, nm, f"h{nm}", f"i{nm}", f"a{nm}")
            else:
                g.load(o, kind)
    loads(hi)
    x, y = (10, 11) if order == "a0a1" else (11, 10)
    vx, vy = lean_val(g.regs[x]), lean_val(g.regs[y])
    params.append(f"(hhi : {vx} {'=' if eq else '≠'} {vy})")
    if eq:
        g.branch(beq, True, f"by rw [g{g.k}_{x}, g{g.k}_{y}]; exact br_beq_t hhi")
        loads(eql)
    else:
        g.branch(beq, False, f"by rw [g{g.k}_{x}, g{g.k}_{y}]; exact br_beq_f hhi")
        loads(nel)
        g.jump(nej)
    g.block(sl, sl + 4)
    for a, b in extra:
        g.block(a, b)
    r = lean_val(g.regs[10])

    def out(sub):
        sub.branch(bz, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; exact br_beq_f hwin")
        sub.jump(fj)
        sub.fail(sub.fail_proof(("prop", "hwin")))
    g.prop_check(f"{r} = 0", "hwin", out)
    g.branch(bz, True, f"by rw [g{g.k}_10, s{g.k}.zero]; exact br_beq_t hwin")
    stmt, proof = finish(g, nxt, sorted(set(CL_KEEP_REGS + [8, 23])), set(g.words))
    which = ["the leaf certificate's start", "the leaf certificate's end", "the intermediate's start",
             "the intermediate's end", "the TSA certificate's start", "the TSA certificate's end",
             "the log key's start", "the log key's end"][i]
    info = {"name": f"sv_win{i}{'e' if eq else 'n'}", "title": f"the timestamp against {which}",
            "doc": f"From 0x{st:X} to 0x{nxt:X}: the timestamp's time isn't "
            + ("before " if tlb else "after ") + which + ", with the high words "
            + ("equal." if eq else "different."),
            "params": params, "stmt": stmt, "proof": proof,
            "binders": RK_BINDERS.replace("op ol : Word}", "op ol lih lil k28 k2c k30 k34 i2h i2l i3h i3l t4h t4l t5h t5l : Word}"),
            "start": st, "import": "C3BootProofs.Proofs.SvRk"}
    return g, info


def ec_start(g):
    """At 0xFBA, after the image signature's `r` and `s` are read: `r` at
    offset 0x138 and `s` at 0x158, each a byte and 31 more."""
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 18: ("U", "out"),
            19: ("U", "bp"), 20: ("S", 0x1320), 21: ("U", "x21"), 26: ("U", "x26"), 27: ("S", 0xA20)}
    words = {e: f"w{e:x}" for e in DPV_WORDS}
    params = start(g, regs, words, {})
    for c, L in ((0x138, "er"), (0x158, "es")):
        g.bytes[c] = f"BitVec.ofNat 8 ({L}.getD 0 0)"
        params.append(f"(b0_{c:x} : n0.mem ({fa(c)}) = BitVec.ofNat 8 ({L}.getD 0 0))")
        g.ranges[c + 1] = (31, f"BitVec.ofNat 8 ({L}.getD (1 + j) 0)")
        params.append(f"(q0_{c + 1:x} : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x{c + 1:X} + j)) = "
                      f"BitVec.ofNat 8 ({L}.getD (1 + j) 0))")
    params += ["(EC0 : SvEcCode M0)"]
    return params


EC_BINDERS = ("{B out bp x21 x26 : Word} {er es : Bytes} "
              + "{" + " ".join(f"w{e:x}" for e in DPV_WORDS) + " : Word} {v : Nat → Word} {n0 : Machine}")
ORD256 = "BitVec.ofNat 32 0x3FCC4288"


def stage_eca1():
    """From 0xFBA to 0x1008: `r` and `s` are in `[1, n)`, and the leaf key's
    encoding starts with 4."""
    g = Gen("EcA1")
    g.generic_alu = True
    params = ec_start(g)
    params += ["(k_in : SvIn B x21 1)"]
    for c, off, nxt, hn in ((0x138, 0xFBA, 0xFD4, "hr"), (0x158, 0xFDA, 0xFF4, "hs")):
        g.block(off, off + 0x12)
        k = g.isr(off + 0x12, c, ORD256, lambda k, c=c: [
            f"  rw [join32 b{k-1}_{c:x} q{k-1}_{c + 1:x}, mb_dataR F fR{k-1} (by decide) (by decide)] at a0_{k}"])
        L = "er" if c == 0x138 else "es"
        prop = f"inScalarRange (b32 {L}) (memBytes M0 ({ORD256}) 32) = true"

        def out(sub, k=k, hn=hn, nxt=nxt):
            sub.set_a0(k, 0, f"ite_eq_right {hn}")
            sub.branch(nxt, False, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
            sub.jump(nxt + 2)
            sub.fail(sub.fail_proof(("prop", hn)), "sv_fail_24a4")
        g.prop_check(prop, hn, out)
        g.set_a0(k, 1, f"ite_eq_left {hn}")
        g.branch(nxt, True, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.load_in(0xFFA, "k_in", "(by decide)")
    g.block(0xFFE, 0x1000)

    def tag(sub):
        sub.branch(0x1000, False, f"by rw [g{sub.k}_10, g{sub.k}_11]; exact br_beq_f fun e => htag ((zext_eq4 _).mp e)")
        sub.jump(0x1004)
        sub.fail(sub.fail_proof(("prop", "htag")), "sv_fail_24a4")
    g.prop_check("M0 x21 = 4", "htag", tag)
    g.branch(0x1000, True, f"by rw [g{g.k}_10, g{g.k}_11, htag]; decide")
    stmt, proof = finish(g, 0x1008, [2, 3, 4, 18, 19, 20, 21, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "sv_eca1", "title": "the image signature's scalars and the key's tag",
            "doc": "From 0xFBA to 0x1008: the image signature's `r` and `s` are in `[1, n)` for P-256's order `n`, "
            "and the leaf key's SEC1 encoding starts with 4, an uncompressed point.",
            "params": params, "stmt": stmt, "proof": proof, "binders": EC_BINDERS, "start": 0xFBA,
            "import": "C3BootProofs.Proofs.SvEc"}
    return g, info


def main():
    stage = sys.argv[1]
    g, info = {"L1": stage_l1, "L2": stage_l2, "L3": stage_l3, "L4": stage_l4, "L5": stage_l5, "L6": stage_l6, "X1": stage_x1, "X2n": stage_x2n, "X2z": stage_x2z, "X2c": stage_x2c,
                **{f"Dp{i}": stage_dpol(i) for i in range(6)}, "Dbc1": stage_dbc1, "Dbc2e": stage_dbc2e, "Dbc2": stage_dbc2, "Dku1": stage_dku1, "Dku2": stage_dku2,
                "Deku1": stage_deku1, "Deku2": stage_deku2, "Deku3": stage_deku3,
                "L7": stage_l7, "L8a": stage_l8a,
                "Imiss": stage_imiss, "Ihit": stage_ihit, "Iend": stage_iend, "Dpv": stage_dpv, "Ts1": stage_ts1, "Tsa1": stage_tsa1, "Tsa2": stage_tsa2, "Tsa3": stage_tsa3,
                "Tsa4n": lambda: stage_tsa4(False), "Tsa4s": lambda: stage_tsa4(True), "Tsa5": stage_tsa5, "Tsaa": stage_tsaa,
                **{f"Tsav{x}": (lambda x=x: stage_tsav(x)) for x in ("ct", "md", "other")},
                "Tsal": stage_tsal, "Tsax": stage_tsax, "Tst1": stage_tst1, "Tst2": stage_tst2,
                "Tst3n": lambda: stage_tst3(False), "Tst3s": lambda: stage_tst3(True),
                **{f"Tst4{x}": (lambda x=x: stage_tst4(x)) for x in TST4_DOC},
                "Tst5n": lambda: stage_tst5(0xA0, False), "Tst5s": lambda: stage_tst5(0xA0, True),
                "Tst6n": lambda: stage_tst5(0xA1, False), "Tst6s": lambda: stage_tst5(0xA1, True),
                "Tsv": stage_tsv, **{f"Tl{x}": (lambda x=x: stage_tl(x)) for x in ("miss", "hit", "end")},
                "Tsig": stage_tsig, "Ck1": stage_ck1,
                "Ck2a": lambda: stage_ck2(False), "Ck2b": lambda: stage_ck2(True),
                "Ckd": stage_ckd, "Cke": stage_cke,
                **{f"Cl{x}": (lambda x=x: stage_cl(x)) for x in ("miss", "hit", "end")},
                "Cs1": stage_cs1, "Csa": stage_csa,
                **{f"Cn{x}": (lambda x=x: stage_cn(x)) for x in ("m", "e", "s")},
                **{f"Cg{x}": (lambda x=x: stage_cg(x)) for x in range(5)},
                **{f"Cm{x}": (lambda x=x: stage_cm(x)) for x in CM_DOC}, "Csx": stage_csx,
                "Cr1e": lambda: stage_cr1(True), "Cr1n": lambda: stage_cr1(False), "Rl": stage_rl, "Rm": stage_rm,
                **{f"Win{i}{x}": (lambda i=i, x=x: stage_win(i, x == "e")) for i in range(8) for x in "en"},
                "EcA1": stage_eca1}[stage]()
    print(HEADER.format(imp=info.get("import", "C3BootProofs.Proofs.SvDer"), title=info["title"], doc=info["doc"]))
    print("\n".join(g.block_defs()))
    print("set_option maxHeartbeats 0 in")
    print(f"theorem {info['name']} " + info.get("binders", "{B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine}"))
    print("    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)")
    print(f"    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x{info.get('start', 0x72):X} (reg n0))")
    print("    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)")
    print("    " + "\n    ".join(info["params"]) + " :")
    print(f"    {info['stmt']} := by")
    print("\n".join(g.out))
    print(info["proof"])
    print("")
    print("end C3.RV32.Sv")


if __name__ == "__main__":
    main()
