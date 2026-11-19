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


def fail_elem(sub, k, oc, dc, hr, null, width, fail_tail):
    """A reader's failing case: the null address at `oc`, then `fail_tail`."""
    sub.emit(f"  obtain ⟨z{hr}, -⟩ := {null}")
    sub.frame_after(k, [(oc, width), (dc + 8, 8)], {oc: ("0", f"z{hr}")})
    fail_tail(sub)
    sub.fail(sub.fail_proof(("eq", hr)))


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

    def emit(self, s):
        self.out.append(self.ind + s[2:] if s.startswith("  ") else s)

    def clone(self):
        c = Gen(self.name)
        for kk, vv in self.__dict__.items():
            c.__dict__[kk] = vv if kk == "blocks" else dict(vv) if isinstance(vv, dict) else list(vv) if isinstance(vv, list) else vv
        c.out = []
        c.mark = 0
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
        for line in self.out[getattr(self, "prev_mark", 0):]:
            mm = re.search(r"obtain ⟨[^⟩]*⟩ := (\w+)\s*$", line)
            if mm:
                consumed.add(mm.group(1))
        prev = [x for x in prev if x not in consumed]
        self.prev_mark = start
        if prev:
            self.out.append(self.ind + "clear " + " ".join(reversed(prev)))
        self.prev_names = names
        self.mark = len(self.out)

    def common(self, k, steps, fr, saves):
        self.emit(f"  have t{k} : Steps n0 n{k} := t{k-1}.trans {steps}")
        self.emit(f"  have fR{k} : ∀ x, SvR B x → n{k}.mem x = n0.mem x := fun x hx => ({fr} x hx).trans (fR{k-1} x hx)")
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
        self.words, self.bytes = neww, newb

    def keep_frame_L(self, k, ranges):
        self.keep_frame(k, ("L", ranges))

    def load_any(self, off):
        """`lbu` whose value no later step needs."""
        text, ln = INSTR[off]
        rd = reg_of(tokens(text)[2])
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: lbu")
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
                out += f"{c[1]} ∧ "
        return out + "True"

    def sc_ok(self, rest):
        """The checks with their witnesses, then `rest`."""
        out = ""
        for c in self.sc:
            if c[0] == "eq":
                bs = " ".join(c[3])
                out += (f"∃ {bs}, " if bs else "") + f"{c[1]} = {c[2]} ∧\n    "
            else:
                out += f"{c[1]} ∧\n    "
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

    def frame_after(self, k, ranges, words, byts=None):
        """Frame facts after a call that kept all but `ranges`, with `words`
        (offset -> (value, proof)) and `byts` written."""
        self.keep_frame(k, ("L", ranges))
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
        return k, f"derElement 0x{tag:X} (memBytes n0.mem ({rp}) ({rl}).toNat)", (rp, rl, inp)

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

    def elem_split(self, k, expr, oc, dc, rd, fail_tail):
        """Splits on `Der::element`'s result; the failing case reads the null
        address and runs `fail_tail` from there. Returns the `DerTlv` name."""
        t = f"tl{k}"
        self.emit(f"  obtain ⟨r{k}, hr{k}⟩ : ∃ r, {expr} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k} with er{k} | {t}")
        self.sc.append(("eq", expr, f".ok {t}", [t], f"hr{k}"))

        self.fork(lambda sub: fail_elem(sub, k, oc, dc, f"hr{k}", f"Er{k} er{k} hr{k}", 17, fail_tail))
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
        L = f"(memBytes n0.mem ({rp}) ({rl}).toNat)"
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
        return k, f"derOptRes 0x{tag:X} (memBytes n0.mem ({rp}) ({rl}).toNat)", (rp, rl, inp)

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
        L = f"(memBytes n0.mem ({rp}) ({rl}).toNat)"
        return k, f"derIntIsOf n0.mem {L} ({rp}) (derElement 2 {L}) (({a1}).extractLsb' 0 8)", (rp, rl, inp)


    def pos(self, off, oc, dc, fail_tail):
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
        L = f"(memBytes n0.mem ({rp}) ({rl}).toNat)"
        t = f"tl{k}"
        self.split_on(k, f"derElement 2 {L}", f"er{k}", t, f".ok {t}", [t],
                      lambda sub: fail_elem(sub, k, oc, dc, f"hr{k}", f"Er{k} er{k} (by rw [hr{k}]; rfl)", 8, fail_tail))
        pv = f"derPosIntOf {L} ({rp}) (.ok {t})"
        k2 = f"{k}b"
        self.emit(f"  obtain ⟨r{k2}, hr{k2}⟩ : ∃ r, {pv} = r := ⟨_, rfl⟩")
        self.emit(f"  rcases r{k2} with er{k2} | ⟨ip{k}, il{k}⟩")
        self.sc.append(("eq", pv, f".ok (ip{k}, il{k})", [f"ip{k}", f"il{k}"], f"hr{k2}"))
        self.fork(lambda sub: fail_elem(sub, k, oc, dc, f"hr{k2}", f"Er{k} er{k2} (by rw [hr{k}, hr{k2}])", 8, fail_tail))
        self.emit(f"  obtain ⟨p0_{k}, p4_{k}⟩ := Ok{k} ip{k} il{k} (by rw [hr{k}, hr{k2}])")
        self.emit(f"  obtain ⟨d8_{k}, d12_{k}⟩ := A{k} {t} hr{k}")
        hl = f"BitVec.ofNat 32 ({t}.header + {t}.len)"
        self.frame_after(k, [(oc, 8), (dc + 8, 8)],
                         {oc: (f"ip{k}", f"p0_{k}"), oc + 4: (f"il{k}", f"p4_{k}"),
                          dc + 8: (f"({rp}) + {hl}", f"d8_{k}"), dc + 12: (f"({rl}) - {hl}", f"d12_{k}")})
        self.slices[(f"({rp}) + {hl}", f"({rl}) - {hl}")] = f"({inp}.restW hr{k})"
        return k, (rp, rl, inp)

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
        return k, f"derElement 0x30 (memBytes n0.mem ({rp}) ({rl}).toNat)", (rp, rl, inp)

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
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k, f"derAlgOf n0.mem ({p}) ({nl})", p, inp

    def sne(self, off, p, pl, q, ql, hp, hq):
        """`<[u8]>::ne` of `pl` bytes at `p` and `ql` at `q`; returns k. The result in
        `a0` is left to the caller."""
        k = self.k = self.k + 1
        self.call_head(k, off, "sv_sneF", f"(pl := {pl}) (ql := {ql})",
                       [f"c{k}", f"s{k}", f"rk{k}", f"a0_{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} s{k-1} sv_at_{off:x} sv_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    g{k-1}_10 g{k-1}_11 g{k-1}_12 g{k-1}_13 {hp} {hq}")
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
        bytes_ = alias_bytes = f"(memBytes n0.mem ({rp}) ({rl}))"
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

    # --- operations -------------------------------------------------------------

    def block(self, start, end):
        """ALU instructions from `start` to `end`."""
        k = self.k = self.k + 1
        ins, off, vals, writes = [], start, dict(self.regs), {}
        vals[0] = ("C", 0)
        while off < end:
            text, ln = INSTR[off]
            ins.append(text)
            tk = tokens(text)
            if tk[0] == ".lui":
                rd = reg_of(tk[1]); v = ("C", int(tk[2], 16))
            elif tk[0] == ".aluImm" and tk[1] == ".add":
                rd = reg_of(tk[2]); v = add(vals.get(reg_of(tk[3])), ("C", int(tk[4], 16)))
            elif tk[0] == ".alu" and tk[1] == ".add":
                rd = reg_of(tk[2]); v = add(vals.get(reg_of(tk[3])), vals.get(reg_of(tk[4])))
            elif tk[0] == ".aluImm" and tk[1] == ".and":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3]))
                v = ("C", x[1] & int(tk[4], 16)) if x is not None and x[0] == "C" else None
            elif tk[0] in (".aluImm", ".alu"):
                rd = reg_of(tk[2]); v = None
            else:
                raise ValueError(text)
            vals[rd] = v
            writes[rd] = v
            off += ln
        blk = f"sv{self.name}{start:x}"
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
            if v is None:
                continue
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by")
            self.emit(f"    rw [rb{k}]; simp +decide only [runBlock, BInstr.run, {blk}, upd, ↓reduceIte, aluEval]")
            self.emit(f"    all_goals (try simp only [{prev}])")
            self.emit(f"    all_goals first | decide | sv_addr")
            new[r] = v
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
        if kind == "sw":
            ww = {e: (sv, f"by rw [W{k}, {srcfact}]" + ("; rfl" if src == 0 else ""))}
            wb = {}
        else:
            if sv[0] == "U" and len(sv) == 3:
                ww, wb = {}, {e: (sv[2], f"by rw [W{k}, {srcfact}, lbu_low]")}
            else:
                ww, wb = {}, {e: (f"({lean_val(sv)}).extractLsb' 0 8", f"by rw [W{k}, {srcfact}]")}
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
        self.keep_frame(k, ("K", dst, N), ww, wb)
        self.end_step()

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

    def fail(self, why_not):
        """Close the failing case at 0x966 with `why_not`, a proof that the
        stage's checks failed."""
        k = self.k
        self.emit(f"  exact .inl ⟨({why_not}), sv_fail F E{k} s{k} t{k} fR{k} V{k} hret g{k}_2 g{k}_18 hO g{k}_3 g{k}_4⟩")

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
        self.keep_regs(k, OID_KEEP, lambda r: f"rk{k} {rname(r)} (by decide) (by decide)")
        return k

    def conclusion(self, off, keep_regs, keep_words, keep_bytes, wit):
        k = self.k
        conj = ["Steps n0 n'", f"St n'.mem SV n' 0x{off:X} (reg n')", "SvCode n'.mem", "SvSaves B n'.mem v",
                "(∀ x, SvR B x → n'.mem x = n0.mem x)"]
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

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

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
    g.emit("  have fR0 : ∀ x, SvR B x → n0.mem x = n0.mem x := fun _ _ => rfl")
    g.emit("  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl")
    g.emit("  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl")
    der = "(memBytes n0.mem lp ll.toNat)"
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
            "params": params, "stmt": stmt, "proof": proof}
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
    g.emit("  have fR0 : ∀ x, SvR B x → n0.mem x = n0.mem x := fun _ _ => rfl")
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
    g.sc.append(("eq", f"derElement 2 (memBytes n0.mem ({rp}) ({rl}).toNat)", f".ok te{k}", [f"te{k}"], f"hte{k}"))
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
        sub.emit(f"  obtain ⟨y0_{ka}, y4_{ka}, y8_{ka}⟩ := R{ka}")
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

    oid = f"memBytes n0.mem op{ka} ol{ka} = memBytes n0.mem (BitVec.ofNat 32 0x3FCC4840) 8"

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
    stmt, proof = finish(g, 0x318, [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                         {0x4C, 0x50, 0x54, 0x58, 0x5C, 0x60, 0x64, 0x68, 0x6C, 0x70, 0x74, 0x78, 0x7C, 0x80, 0x84,
                          0x180, 0x184}, set())
    binders = ("{B out bp rootp dg lp ll rp rl sgl orl orp trp tcl sgp arp arl trl : Word} {v : Nat → Word} "
               "{n0 : Machine}")
    info = {"name": "sv_l4", "title": "the issuer and the validity",
            "doc": "From 0x266 to the subject at 0x318: the issuer, and the validity, a sequence of exactly two "
            "times.", "params": params, "stmt": stmt, "proof": proof, "binders": binders, "start": 0x266,
            "import": "C3BootProofs.Proofs.SvCongr"}
    return g, info

def main():
    stage = sys.argv[1]
    g, info = {"L1": stage_l1, "L2": stage_l2, "L3": stage_l3, "L4": stage_l4}[stage]()
    print(HEADER.format(imp=info.get("import", "C3BootProofs.Proofs.SvDer"), title=info["title"], doc=info["doc"]))
    print("\n".join(g.block_defs()))
    print("set_option maxHeartbeats 0 in")
    print(f"theorem {info['name']} " + info.get("binders", "{B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine}"))
    print("    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)")
    print(f"    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x{info.get('start', 0x72):X} (reg n0))")
    print("    " + "\n    ".join(info["params"]) + " :")
    print(f"    {info['stmt']} := by")
    print("\n".join(g.out))
    print(info["proof"])
    print("")
    print("end C3.RV32.Sv")


if __name__ == "__main__":
    main()
