#!/usr/bin/env python3
"""Writes the straight-line stages of the `p384_verify_prehash` proof.

Each stage is a list of operations: blocks of ALU instructions, calls through
the wrappers in `Pv384Lib.lean`, and stores. The script follows the registers
and the 12-limb values in the frame through the operations and writes a Lean
proof that tracks the same facts, one `have` per fact per step.

Usage: python3 scripts/gen-p384-verify.py STAGE > C3BootProofs/Proofs/Pv384<STAGE>.lean
"""

import re
import sys

AT = open("C3BootProofs/Proofs/Pv384At.lean").read()
INSTR = {}
for mm in re.finditer(
    r"theorem pv_at_([0-9a-f]+) : fetchRel p384VerifyPrehashCode 0x[0-9A-F]+ = some \((.*), (\d+)\) := by decide", AT
):
    INSTR[int(mm.group(1), 16)] = (mm.group(2), int(mm.group(3)))

REGS = {"x0": 0, "ra": 1, "sp": 2, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17,
        "t0": 5, "t1": 6}
KEEP = [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]


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


def binstr(text):
    t = text
    t = t.replace(".load .lw ", ".lw ").replace(".load .lbu ", ".lbu ")
    t = t.replace(".store .sw ", ".sw ").replace(".store .sb ", ".sb ")
    return t


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


def lean_val(v):
    if v[0] == "S":
        return "B + 0x420" if v[1] == 0 else f"B + 0x420 + BitVec.ofNat 32 0x{v[1]:X}"
    if v[0] == "C":
        return f"BitVec.ofNat 32 0x{v[1]:X}"
    return v[1]


ENV3_WRAPPERS = {"pv_umin", "pv_low", "pv_ufg", "pv_ude", "pv_norm", "pv_eq"}


class Gen:
    def __init__(self, name, env3=False):
        self.name = name
        self.env3 = env3
        self.envt = "PvEnv3" if env3 else "PvEnv"
        self.k = 0
        self.out = []
        self.blocks = []
        self.regs = {}
        self.acc = {}
        self.bytes = {}
        self.words = {}

    def emit(self, s):
        self.out.append(s)

    def env(self, k):
        """The `PvEnv` of state k."""
        return f"E{k}.E" if self.env3 else f"E{k}"

    def end_step(self):
        """Clears the facts of the step before the one just finished, so that tactics
        such as `omega` see a context of constant size."""
        start = getattr(self, "mark", 0)
        names = []
        for line in self.out[start:]:
            mm = re.match(r"  have (\w+)", line)
            if mm:
                names.append(mm.group(1))
            mm = re.match(r"  obtain ⟨([^⟩]*)⟩", line)
            if mm:
                names += [x.strip() for x in mm.group(1).split(",") if not re.fullmatch(r"n\d+", x.strip())]
        prev = getattr(self, "prev_names", [])
        if prev:
            self.out.append("  clear " + " ".join(reversed(prev)))
        self.prev_names = names
        self.mark = len(self.out)

    def facts(self, k):
        return [f"g{k}_{r}" for r in sorted(self.regs)]

    # The register facts for state k after a step in which `kind` says how registers
    # changed.
    def reg_facts(self, k, kind, blk=None, writes=None):
        new = {}
        for r, v in sorted(self.regs.items()):
            if kind == "blk" and r not in writes:
                self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by")
                self.emit(f"    rw [rb{k}, runBlock_reg _ _ _ {rname(r)} s{k-1}.zero (by decide), g{k-1}_{r}]")
                new[r] = v
            elif kind == "call" and r in KEEP:
                self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [P{k}.regs {rname(r)} (by decide), g{k-1}_{r}]")
                new[r] = v
            elif kind == "same":
                self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [rg{k} {rname(r)}, g{k-1}_{r}]")
                new[r] = v
        if kind == "blk":
            prev = ", ".join(self.facts(k - 1) + [f"s{k-1}.zero", "BitVec.zero_add"])
            for r, v in sorted(writes.items()):
                if v is None:
                    continue
                self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by")
                self.emit(f"    rw [rb{k}]; simp +decide only [runBlock, BInstr.run, {blk}, upd, ↓reduceIte, aluEval] <;>")
                self.emit(f"    (try simp only [{prev}]) <;> pv_val")
                new[r] = v
        self.regs = new

    def mem_facts(self, k, c, w, written_acc=None, written_bytes=None, written_words=None):
        """Facts after a step that wrote the `w` bytes at offset `c`."""
        written_acc = written_acc or {}
        written_bytes = written_bytes or {}
        written_words = written_words or {}
        new = {}
        for d, v in sorted(self.acc.items()):
            if d in written_acc:
                continue
            if d + 48 <= c or c + w <= d:
                self.emit(f"  have a{k}_{d:x} : accV n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12 = {v} :=")
                self.emit(f"    (K{k}.acc (by decide) (by decide)).trans a{k-1}_{d:x}")
                new[d] = v
        for d, (v, proof) in sorted(written_acc.items()):
            self.emit(f"  have a{k}_{d:x} : accV n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12 = {v} := by")
            for line in proof:
                self.emit(f"    {line}")
            new[d] = v
        self.acc = new
        newb = {}
        for e, v in sorted(self.bytes.items()):
            if e in written_bytes:
                continue
            if e + 1 <= c or c + w <= e:
                self.emit(f"  have b{k}_{e:x} : n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v} := by")
                self.emit(f"    rw [K{k} _ (by decide) (by decide), b{k-1}_{e:x}]")
                newb[e] = v
        for e, (v, proof) in sorted(written_bytes.items()):
            self.emit(f"  have b{k}_{e:x} : n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v} := by")
            for line in proof:
                self.emit(f"    {line}")
            newb[e] = v
        self.bytes = newb
        neww = {}
        for e, v in sorted(self.words.items()):
            if e in written_words:
                continue
            if e + 4 <= c or c + w <= e:
                self.emit(f"  have w{k}_{e:x} : memLoad32 n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v} := by")
                self.emit(f"    rw [← w{k-1}_{e:x}]; exact memLoad32_congr fun j hj => by")
                self.emit(f"      rw [add_ofNat_assoc]; exact K{k} _ (by omega) (by omega)")
                neww[e] = v
        for e, (v, proof) in sorted(written_words.items()):
            self.emit(f"  have w{k}_{e:x} : memLoad32 n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v} := by")
            for line in proof:
                self.emit(f"    {line}")
            neww[e] = v
        self.words = neww

    def common(self, k, steps):
        self.emit(f"  have t{k} : Steps n0 n{k} := t{k-1}.trans {steps}")
        self.emit(f"  have fR{k} : ∀ x, PvR B x → n{k}.mem x = n0.mem x := fun x hx => (fr{k} x hx).trans (fR{k-1} x hx)")

    def block(self, start, end, writes_extra=None):
        """ALU instructions from `start` to `end`, followed by a step at `end`."""
        k = self.k = self.k + 1
        ins = []
        off = start
        vals = dict(self.regs)
        vals[0] = ("C", 0)
        writes = {}
        while off < end:
            text, ln = INSTR[off]
            ins.append(binstr(text))
            tk = tokens(text)
            if tk[0] == ".lui":
                rd = reg_of(tk[1]); v = ("C", int(tk[2], 16))
            elif tk[0] == ".aluImm" and tk[1] == ".add":
                rd = reg_of(tk[2]); v = add(vals.get(reg_of(tk[3])), ("C", int(tk[4], 16)))
            elif tk[0] == ".alu" and tk[1] == ".add":
                rd = reg_of(tk[2]); v = add(vals.get(reg_of(tk[3])), vals.get(reg_of(tk[4])))
            elif tk[0] == ".aluImm":
                rd = reg_of(tk[2]); v = None
            else:
                raise ValueError(text)
            vals[rd] = v
            writes[rd] = v
            off += ln
        if writes_extra:
            writes.update(writes_extra)
        blk = f"pv{self.name}{start:x}"
        self.blocks.append((blk, start, end, ins))
        n = len(ins)
        self.emit(f"  -- 0x{start:X}")
        self.emit(f"  obtain ⟨n{k}, c{k}, u{k}⟩ := s{k-1}.block {blk} {self.env(k-1)}.C.self {blk}_end")
        self.emit(f"    ⟨{', '.join(['trivial'] * (n + 1))}⟩")
        self.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        self.emit(f"  have s{k} : St n{k}.mem PV n{k} 0x{end:X} (reg n{k}) := ⟨u{k}.pc, rfl, fun _ => rfl⟩")
        self.emit(f"  have E{k} : {self.envt} n{k}.mem := by rw [m{k}]; exact E{k-1}")
        self.emit(f"  have rb{k} : ∀ q, reg n{k} q = (runBlock {blk} (n{k-1}.mem, reg n{k-1})).2 q := fun q => by rw [u{k}.regs]")
        self.emit(f"  have fr{k} : ∀ x, PvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        self.emit(f"  have K{k} : PvKeep B n{k-1}.mem n{k}.mem 0 0 := fun e _ _ => by rw [m{k}]")
        self.common(k, f"c{k}")
        self.reg_facts(k, "blk", blk, writes)
        self.mem_facts(k, 0, 0)
        self.end_step()
        return k

    def call(self, wrapper, off, args, c, w, written_acc=None, written_bytes=None, extra_regs=None, pre=None):
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: {wrapper}")
        for line in pre or []:
            self.emit(f"  {line}")
        ev = f"E{k-1}" if (wrapper in ENV3_WRAPPERS or not self.env3) else f"E{k-1}.E"
        self.emit(f"  obtain ⟨n{k}, P{k}, K{k}, V{k}⟩ := {wrapper} F {ev} s{k-1} pv_at_{off:x} pv_at_{off+4:x} (by decide) (by decide)")
        self.emit(f"    {args}")
        self.emit(f"  have s{k} := P{k}.st")
        self.emit(f"  have fr{k} := P{k}.fr")
        self.emit(f"  have E{k} : {self.envt} n{k}.mem := E{k-1}.fr F fr{k}")
        self.common(k, f"P{k}.steps")
        self.reg_facts(k, "call")
        for r, (v, proof) in (extra_regs or {}).items():
            self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by {proof}")
            self.regs[r] = v
        self.mem_facts(k, c, w, written_acc, written_bytes)
        self.end_step()
        return k

    def store(self, wrapper, off, ln, args, c, w, written_bytes=None, written_words=None):
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: {wrapper}")
        self.emit(f"  obtain ⟨n{k}, d{k}, s{k}, _E{k}, fr{k}, K{k}, V{k}, rg{k}⟩ := {wrapper} F {self.env(k-1)} s{k-1} pv_at_{off:x} (off' := 0x{off+ln:X}) (c := 0x{c:X}) (by decide)")
        self.emit(f"    {args}")
        self.emit(f"  have E{k} : {self.envt} n{k}.mem := E{k-1}.fr F fr{k}")
        self.common(k, f"d{k}")
        self.reg_facts(k, "same")
        self.mem_facts(k, c, w, written_bytes=written_bytes, written_words=written_words)
        self.end_step()
        return k

    def conclusion(self, off):
        """The facts at the end, as a conjunction, and the term that proves it."""
        k = self.k
        conj = [f"Steps n0 n'", f"St n'.mem PV n' 0x{off:X} (reg n')", f"{self.envt} n'.mem",
                "(∀ x, PvR B x → n'.mem x = n0.mem x)"]
        terms = [f"t{k}", f"s{k}", f"E{k}", f"fR{k}"]
        for r, v in sorted(self.regs.items()):
            conj.append(f"reg n' {rname(r)} = {lean_val(v)}"); terms.append(f"g{k}_{r}")
        for d, v in sorted(self.acc.items()):
            conj.append(f"accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12 = {v}"); terms.append(f"a{k}_{d:x}")
        for e, v in sorted(self.bytes.items()):
            conj.append(f"n'.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v}"); terms.append(f"b{k}_{e:x}")
        for e, v in sorted(self.words.items()):
            conj.append(f"memLoad32 n'.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v}"); terms.append(f"w{k}_{e:x}")
        stmt = "∃ n', " + " ∧\n      ".join(conj)
        proof = f"  exact ⟨n{k}, " + ", ".join(terms) + "⟩"
        return stmt, proof

    def block_defs(self):
        lines = []
        for blk, start, end, ins in self.blocks:
            lines.append(f"def {blk} : List BInstr :=")
            lines.append("  [" + ", ".join(ins) + "]")
            lines.append(f"theorem {blk}_end : blockEnd p384VerifyPrehashCode 0x{start:X} {blk} = some 0x{end:X} := by decide")
            lines.append("")
        return lines


def S(o):
    return ("S", o)


def C(c):
    return ("C", c)


def copy_facts(g, dst, src, N, vref):
    """The 12-limb facts a copy of `N` bytes from offset `src` to `dst` leaves."""
    acc = {}
    for d, v in g.acc.items():
        if src <= d and d + 48 <= src + N:
            nd = dst + (d - src)
            acc[nd] = (v, [
                f"rw [← a{g.k}_{d:x}]",
                "exact accV_S 12 fun q hq => by",
                f"  have := {vref} (0x{d - src:X} + q) (by omega)",
                f"  rwa [show 0x{dst:X} + (0x{d - src:X} + q) = 0x{nd:X} + q by omega,",
                f"    show 0x{src:X} + (0x{d - src:X} + q) = 0x{d:X} + q by omega] at this",
            ])
    return acc


DATA_FIELD = {"p384MontOneData": "one", "p384OrderData": "nmod", "p384ScalarR2Data": "r2",
              "p384IdentityData": "idp", "p384GData": "g", "u12OneData": "u1"}


class Ops:
    def __init__(self, g):
        self.g = g

    def mc(self, off, dst, src, N):
        g = self.g
        g.call("pv_mc", off, f"g{g.k}_2 g{g.k}_10 g{g.k}_11 g{g.k}_12 (by decide) (by decide) (by decide)", dst, N,
               copy_facts(g, dst, src, N, f"V{g.k + 1}"))

    def mcK(self, off, dst, K, N, data):
        g = self.g
        acc = {dst: (f"dataVal {data} 0 12", [
            f"rw [show BitVec.ofNat 32 0x{K:X} = BitVec.ofNat 32 0x{K:X} + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm] at V{g.k + 1}",
            f"rw [accV_K 12 fun q hq => V{g.k + 1} q (by omega)]",
            f"exact code_accV (d := {data}) {g.env(g.k)}.D2.{DATA_FIELD[data]} 0 12 (by decide)",
        ])}
        g.call("pv_mcK", off, f"g{g.k}_2 g{g.k}_10 g{g.k}_11 g{g.k}_12 (by decide) (by decide) (by decide)", dst, N, acc)

    def csel(self, off, dst, a, b):
        """Select with a choice of 0, so the limbs at offset `a`; `b` is a constant."""
        g = self.g
        acc = {dst: (g.acc[a], [f"rw [V{g.k + 1}, ite_eq_right (by decide), a{g.k}_{a:x}]"])}
        g.call("pv_csel", off,
               f"g{g.k}_2 g{g.k}_10 g{g.k}_11 g{g.k}_12 g{g.k}_13 (.inl (by decide)) (by decide)\n"
               f"    (pv_lowS F (k := 0x60) (by decide) (by decide) (by decide))\n"
               f"    (pv_lowK F (n := 48) (k := 0x60) (by decide) (by decide) (by decide)) (by decide)\n"
               f"    (by rw [pv_at F 0x{a:X} (by decide)]; have := F.hi; omega)", dst, 48, acc)

    def sn(self, off, dst, x):
        g = self.g
        acc = {dst: (f"{g.acc[x]} * 2 ^ 384 % n384", [f"rw [V{g.k + 1}, a{g.k}_{x:x}]"])}
        g.call("pv_sn", off, f"g{g.k}_2 g{g.k}_10 g{g.k}_11 (by decide) (by decide) (by decide) (by decide)", dst, 48, acc)

    def nz(self, off, dst, x, h0, hn):
        g = self.g
        k = g.k
        acc = copy_facts(g, dst, x, 48, f"V{k + 1}.1")
        byt = {dst + 0x30: ("1", [f"rw [show (0x{dst + 0x30:X} : Nat) = 0x{dst:X} + 0x30 from rfl, V{k + 1}.2, ite_eq_right hnz{k + 1}]"])}
        pre = [f"have hnz{k + 1} : ¬ ∀ i : Nat, i < 12 → memLoad32 n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{x:X} + BitVec.ofNat 32 (4 * i)) = 0 :=",
               f"  fun h => n3_mont_ne {h0} {hn} (by rw [← a{k}_{x:x}]; exact (accV_eq_zero_iff 12).2 h)"]
        g.call("pv_nz", off, f"g{k}_2 g{k}_10 g{k}_11 (by decide) (by decide) (by decide) (by decide)", dst, 49, acc, byt,
               pre=pre)

    def cu(self, off, dst, src):
        g = self.g
        g.call("pv_cu", off, f"g{g.k}_2 g{g.k}_10 g{g.k}_11 (by decide) (by decide) (by decide) b{g.k}_{src + 0x30:x}", dst, 48,
               copy_facts(g, dst, src, 48, f"V{g.k + 1}"))

    def b2s(self, off, dst):
        g = self.g
        k = g.k
        acc = {dst: ("beNat (memBytes n0.mem ph (min len 48)) * 2 ^ 384 % n384", [
            f"rw [V{k + 1}, memBytes_congr fun i hi => fR{k} _ (sph.symm.subR (c := i) (l := 1) (by omega))]"])}
        g.call("pv_b2s", off, f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 (by decide) (by decide) hph sph", dst, 48, acc)

    def bb(self, off, val, proof):
        g = self.g
        g.call("pv_bb", off, f"g{g.k}_2", 0, 0, extra_regs={10: (val, proof.format(k=g.k + 1, p=g.k))})

    def inz(self, off, x, h0, hn):
        g = self.g
        k = g.k
        pre = [f"have hnz{k + 1} : ¬ ∀ i : Nat, i < 12 → memLoad32 n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{x:X} + BitVec.ofNat 32 (4 * i)) = 0 :=",
               f"  fun h => n3_mont_ne {h0} {hn} (by rw [← a{k}_{x:x}]; exact (accV_eq_zero_iff 12).2 h)"]
        g.call("pv_inz", off, f"g{k}_2 g{k}_10 (by decide) (by decide)", 0, 0,
               extra_regs={10: (C(1), f"rw [V{k + 1}, ite_eq_right hnz{k + 1}]; rfl")}, pre=pre)

    def sw(self, off, base, imm, src, c):
        g = self.g
        k = g.k
        g.store("pv_sw", off, INSTR[off][1], f"(by rw [g{k}_{base}]; pv_addr) (by decide) (by decide)", c, 4,
                written_words={c: (lean_val(g.regs[src]), [f"rw [V{k + 1}, g{k}_{src}]"])})

    def ms0(self, off, dst, N):
        """`memset` of `N` zero bytes at `dst`: zero limbs, and zero sign bytes."""
        g = self.g
        k = g.k
        acc = {dst: ("0", [f"exact accV_zero_S 12 fun q hq => V{k + 1} q (by omega)"])}
        byt = {}
        if dst + 0x30 < dst + N:
            byt[dst + 0x30] = ("0", [f"exact V{k + 1} 0x30 (by decide)"])
        g.call("pv_ms", off, f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 (by decide)", dst, N, acc, byt)

    def sb0(self, off, base, c):
        g = self.g
        k = g.k
        g.store("pv_sb", off, INSTR[off][1], f"(by rw [g{k}_{base}]; pv_addr) (by decide)", c, 1,
                written_bytes={c: ("0", [f"rw [V{k + 1}, s{k}.zero]; rfl"])})


def params_of(g, off, extra=""):
    """Hypotheses for state 0 from the facts a generator starts with."""
    ps = ["{n0 : Machine}", "(F : Fr B 0x21A0)", f"(E0 : {g.envt} n0.mem)", f"(s0 : St n0.mem PV n0 0x{off:X} (reg n0))"]
    for r, v in sorted(g.regs.items()):
        ps.append(f"(g0_{r} : reg n0 {rname(r)} = {lean_val(v)})")
    for d, v in sorted(g.acc.items()):
        ps.append(f"(a0_{d:x} : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12 = {v})")
    for e, v in sorted(g.bytes.items()):
        ps.append(f"(b0_{e:x} : n0.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v})")
    for e, v in sorted(g.words.items()):
        ps.append(f"(w0_{e:x} : memLoad32 n0.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v})")
    return "\n    ".join(ps) + extra


def stage_c0():
    gb, _ = stage_b()
    g = Gen("C0", env3=True)
    g.regs = dict(gb.regs)
    for r in (3, 4, 25, 26, 27):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {d: v for d, v in gb.acc.items() if d in (0x120, 0x150, 0x180, 0x1B0, 0x1E0, 0x210, 0xD50, 0xE10, 0xE40, 0x1714)}
    g.bytes = dict(gb.bytes)
    g.words = dict(gb.words)
    params = params_of(g, 0x3B0)
    o = Ops(g)
    o.sb0(0x3B0, 8, 0xD80)
    g.block(0x3B4, 0x3BC); o.ms0(0x3BC, 0x270, 0x34)
    g.block(0x3C4, 0x3D2); o.mcK(0x3D2, 0x17A4, 0x3FCC4D88, 0x30, "p384ScalarR2Data")
    g.block(0x3DA, 0x3DC)
    o.sb0(0x3DC, 23, 0x17D4)
    g.block(0x3E0, 0x3E8)
    info = {
        "end": 0x3E8, "name": "pv_stC0", "title": "the inversion's start",
        "doc": "From 0x3B0 to 0x3E8: `g`'s and `e`'s sign bytes, `d` zeroed, `e` set to `2^768 mod n`,\nand the loop's `δ`, step budget, and bound.",
        "thmdoc": "**Stage C0**, from 0x3B0 to 0x3E8: the start of the inversion of `s`.",
        "params": "{B ph : Word} {len X Y R Sg : Nat} " + params,
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl"],
        "import": "C3BootProofs.Proofs.Pv384Lib2",
    }
    return g, info


def stage_b():
    g = Gen("B")
    g.regs = {2: S(0), 8: S(0xD80), 18: C(0), 19: ("U", "BitVec.ofNat 32 len"), 20: ("U", "ph")}
    for r in (3, 4, 25, 26, 27):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {0x58: "X", 0x88: "Y", 0x270: "R", 0x17A4: "Sg"}
    o = Ops(g)
    g.block(0x156, 0x16E); o.mc(0x16E, 0x1294, 0x270, 0x30)
    g.block(0x176, 0x18A); o.mc(0x18A, 0x12C4, 0x17A4, 0x30)
    g.block(0x192, 0x1A6); o.mc(0x1A6, 0xE10, 0x1294, 0x60)
    g.block(0x1AE, 0x1BC); o.mc(0x1BC, 0x3F0, 0xE10, 0x60)
    g.block(0x1C4, 0x1D6); o.mc(0x1D6, 0x12C4, 0x88, 0x30)
    g.block(0x1DE, 0x1EC); o.mc(0x1EC, 0x1294, 0x58, 0x30)
    g.block(0x1F4, 0x20C); o.mcK(0x20C, 0x12F4, 0x3FCC44A0, 0x30, "p384MontOneData")
    g.block(0x214, 0x216); o.bb(0x216, C(0), "rw [V{k}, g{p}_10]; rfl")
    g.block(0x21E, 0x238, {9: C(0), 13: C(0)}); o.csel(0x238, 0x120, 0x1294, 0x3FCC44D0)
    g.block(0x240, 0x24A); o.csel(0x24A, 0x150, 0x12C4, 0x3FCC4500)
    g.block(0x252, 0x25C); o.csel(0x25C, 0x180, 0x12F4, 0x3FCC4530)
    g.block(0x264, 0x26E); o.sn(0x26E, 0x1294, 0x3F0)
    g.block(0x276, 0x286); o.nz(0x286, 0xE10, 0x1294, "hR0", "hRn")
    g.block(0x28E, 0x29E); o.cu(0x29E, 0x1294, 0xE10)
    g.block(0x2A6, 0x2BC); o.sn(0x2BC, 0x17A4, 0x420)
    g.block(0x2C4, 0x2D4); o.nz(0x2D4, 0xE10, 0x17A4, "hS0", "hSn")
    g.block(0x2DC, 0x2E6); o.cu(0x2E6, 0x12C4, 0xE10)
    g.block(0x2EE, 0x2FC); o.mc(0x2FC, 0x1B0, 0x1294, 0x30)
    g.block(0x304, 0x30C); o.mc(0x30C, 0x1E0, 0x12C4, 0x30)
    g.block(0x314, 0x31A); o.b2s(0x31A, 0x210)
    g.block(0x322, 0x338); o.mcK(0x338, 0xE10, 0x3FCC4D28, 0x30, "p384OrderData")
    g.block(0x340, 0x350)
    o.sw(0x350, 8, 0xF0, 20, 0xE70)
    o.sw(0x354, 8, 0xF4, 22, 0xE74)
    g.block(0x358, 0x36A); o.mcK(0x36A, 0xE40, 0x3FCC4D88, 0x30, "p384ScalarR2Data")
    g.block(0x372, 0x374); o.inz(0x374, 0x1E0, "hS0", "hSn")
    g.block(0x37C, 0x38E, {24: C(1)}); o.mcK(0x38E, 0x1714, 0x3FCC4D28, 0x30, "p384OrderData")
    o.sb0(0x396, 23, 0x1744)
    g.block(0x39A, 0x3A8); o.mc(0x3A8, 0xD50, 0x1E0, 0x30)
    info = {
        "end": 0x3B0, "name": "pv_stB", "title": "the inputs to the inversion",
        "doc": "From 0x156 to 0x3B0: the key as a projective point, `r`, `s`, and the\nprehash as scalars in Montgomery form, and the inversion's modulus.",
        "thmdoc": "**Stage B**, from 0x156 to 0x3B0: copy the key's coordinates into a projective\npoint, put `r` and `s` in Montgomery form and check they are nonzero, read the prehash\nas a scalar, and set up the inversion of `s`.",
        "params": """{n0 : Machine} {B ph : Word} {len X Y R Sg : Nat} (F : Fr B 0x21A0) (E0 : PvEnv n0.mem)
    (s0 : St n0.mem PV n0 0x156 (reg n0)) (g0_2 : reg n0 sp = B + 0x420)
    (g0_8 : reg n0 (8 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80) (g0_18 : reg n0 (18 : Fin 32) = BitVec.ofNat 32 0x0)
    (g0_19 : reg n0 (19 : Fin 32) = BitVec.ofNat 32 len) (g0_20 : reg n0 (20 : Fin 32) = ph)
    (a0_58 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x58) 12 = X)
    (a0_88 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x88) 12 = Y)
    (a0_270 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12 = R)
    (a0_17a4 : accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x17A4) 12 = Sg)
    (hR0 : R ≠ 0) (hRn : R < n384) (hS0 : Sg ≠ 0) (hSn : Sg < n384) (hph : ph.toNat + len < 2 ^ 32)
    (sph : Sep ph len (B + 0xFFFFFE60) 0x230C)""",
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl"]
                 + [f"have g0_{r} : reg n0 ({r} : Fin 32) = reg n0 ({r} : Fin 32) := rfl" for r in (3, 4, 25, 26, 27)],
    }
    return g, info


HEADER = """import {imp}

/-!
# `p384_verify_prehash`: {title}

Generated by `scripts/gen-p384-verify.py {stage}`. {doc}
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
"""


def main():
    stage = sys.argv[1]
    g, info = {"B": stage_b, "C0": stage_c0}[stage]()
    stmt, proof = g.conclusion(info["end"])
    print(HEADER.format(imp=info.get("import", "C3BootProofs.Proofs.Pv384Lib"), title=info["title"], stage=stage,
                        doc=info["doc"]))
    print("\n".join(g.block_defs()))
    print("set_option maxHeartbeats 0 in")
    print(f"/-- {info['thmdoc']} -/")
    print(f"theorem {info['name']} {info['params']} :")
    print(f"    {stmt} := by")
    for line in info["intro"]:
        print(f"  {line}")
    print("\n".join(g.out))
    print(proof)
    print("")
    print("end C3.RV32.Pv")


if __name__ == "__main__":
    main()
