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

    def emit(self, s):
        self.out.append(self.ind + s[2:] if s.startswith("  ") else s)

    def clone(self):
        c = Gen(self.name)
        for kk, vv in self.__dict__.items():
            c.__dict__[kk] = dict(vv) if isinstance(vv, dict) else list(vv) if isinstance(vv, list) else vv
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
        names = [x for x in names if re.fullmatch(r"[A-Za-z_][\w']*", x) and not x.startswith("keep_")
                 and not x.startswith("ht_") and not x.startswith("hz_") and not x.startswith("hr") and not re.fullmatch(r"r\d+", x)]
        prev = getattr(self, "prev_names", [])
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
            self.emit(f"    all_goals sv_addr")
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
    keep_regs = [2, 3, 4, 10, 11, 12, 18, 19, 22, 25, 27]
    conj, terms = g.conclusion(0xD0, keep_regs, set(g.words), set(g.bytes), [])
    stmt = (f"(¬ ({sc}) ∧ SvErrRet B out v n0) ∨\n    (∃ t, derElement 0x30 {der} = .ok t ∧ "
            f"ll - BitVec.ofNat 32 (t.header + t.len) = 0 ∧\n      ∃ n', " + " ∧\n        ".join(c.replace(t, "t") for c in conj) + ")")
    proof = f"  exact .inr ⟨{t}, hr{k}, hz_{rest_k}, n{g.k}, " + ", ".join(terms) + "⟩"
    info = {"name": "sv_l1", "title": "the certificate", "doc": "From the call to `Der::sequence` over the leaf "
            "certificate at 0x72 to the call to `Der::element` for the `tbsCertificate` at 0xD0: the "
            "certificate is one `SEQUENCE` that fills the bytes.",
            "params": params, "stmt": stmt, "proof": proof}
    return g, info


def main():
    stage = sys.argv[1]
    g, info = {"L1": stage_l1}[stage]()
    print(HEADER.format(imp="C3BootProofs.Proofs.SvDer", title=info["title"], doc=info["doc"]))
    print("\n".join(g.block_defs()))
    print("set_option maxHeartbeats 0 in")
    print(f"theorem {info['name']} {{B out bp rootp dg lp ll : Word}} {{v : Nat → Word}} {{n0 : Machine}}")
    print("    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)")
    print("    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x72 (reg n0))")
    print("    " + "\n    ".join(info["params"]) + " :")
    print(f"    {info['stmt']} := by")
    print("\n".join(g.out))
    print(info["proof"])
    print("")
    print("end C3.RV32.Sv")


if __name__ == "__main__":
    main()
