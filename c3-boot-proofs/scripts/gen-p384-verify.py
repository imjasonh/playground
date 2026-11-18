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
    if isinstance(v, str):
        return v
    if v[0] == "S":
        return "B + 0x420" if v[1] == 0 else f"B + 0x420 + BitVec.ofNat 32 0x{v[1]:X}"
    if v[0] == "C":
        return f"BitVec.ofNat 32 0x{v[1]:X}"
    return v[1]


ENV3_WRAPPERS = {"pv_umin", "pv_low", "pv_ufg", "pv_ude", "pv_norm", "pv_eq"}
ENV4_WRAPPERS = {"pv_smul", "pv_pd", "pv_pa"}
ENV5_WRAPPERS = {"pv_za", "pv_mr", "pv_tbb", "pv_rev", "pv_wf"}
ENV_SUFFIX = {(5, 5): "", (5, 4): ".E", (5, 3): ".E.E", (5, 1): ".E.E.E",
              (4, 4): "", (4, 3): ".E", (4, 1): ".E.E", (3, 3): "", (3, 1): ".E", (1, 1): ""}


def wrapper_level(w):
    return 5 if w in ENV5_WRAPPERS else 4 if w in ENV4_WRAPPERS else 3 if w in ENV3_WRAPPERS else 1


class Gen:
    def __init__(self, name, env3=False, env4=False):
        self.name = name
        self.lvl = 4 if env4 else 3 if env3 else 1
        self.env3 = self.lvl >= 3
        self.envt = {1: "PvEnv", 3: "PvEnv3", 4: "PvEnv4"}[self.lvl]
        self.k = 0
        self.out = []
        self.blocks = []
        self.regs = {}
        self.acc = {}
        self.bytes = {}
        self.words = {}
        self.sv = {}
        self.mbf = {}

    def emit(self, s):
        self.out.append(s)

    def env(self, k):
        """The `PvEnv` of state k."""
        return f"E{k}{ENV_SUFFIX[(self.lvl, 1)]}"

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
        names = [x for x in names if not x.startswith("keep_")]
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
            extra = ["BitVec.reduceMul"] if any(".mul" in str(i) for b in self.blocks if b[0] == blk for i in b[3]) else []
            prev = ", ".join(self.facts(k - 1) + [f"s{k-1}.zero", "BitVec.zero_add"] + extra)
            for r, v in sorted(writes.items()):
                if v is None:
                    continue
                self.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by")
                self.emit(f"    rw [rb{k}]; simp +decide only [runBlock, BInstr.run, {blk}, upd, ↓reduceIte, aluEval] <;>")
                self.emit(f"    (try simp only [{prev}]) <;> pv_val")
                new[r] = v
        self.regs = new

    def mbf_stmt(self, k, d, N, kind, v):
        mb = f"memBytes n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 0x{N:X}"
        return {"leN": f"leN ({mb}) = {v}", "leNr": f"leN ({mb}).reverse = {v}", "list": f"{mb} = {v}"}[kind]

    def mem_facts(self, k, c, w, written_acc=None, written_bytes=None, written_words=None, written_sv=None,
                  written_mbf=None):
        """Facts after a step that wrote the `w` bytes at offset `c`."""
        written_mbf = written_mbf or {}
        newm = {}
        for d, (N, kind, v) in sorted(self.mbf.items()):
            if d in written_mbf:
                continue
            if d + N <= c or c + w <= d:
                self.emit(f"  have mb{k}_{d:x} : {self.mbf_stmt(k, d, N, kind, v)} := by")
                self.emit(f"    rw [memBytes_keep K{k} (by decide) (by decide)]; exact mb{k-1}_{d:x}")
                newm[d] = (N, kind, v)
        for d, (N, kind, v, proof) in sorted(written_mbf.items()):
            self.emit(f"  have mb{k}_{d:x} : {self.mbf_stmt(k, d, N, kind, v)} := by")
            for line in proof:
                self.emit(f"    {line}")
            newm[d] = (N, kind, v)
        self.mbf = newm
        written_sv = written_sv or {}
        newsv = {}
        for d, v in sorted(self.sv.items()):
            if d in written_sv:
                continue
            if d + 49 <= c or c + w <= d:
                self.emit(f"  have v{k}_{d:x} : sgnVal (n{k}.mem (B + 0x420 + BitVec.ofNat 32 (0x{d:X} + 0x30))).toNat")
                self.emit(f"      (accV n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12) = {v} := by")
                self.emit(f"    rw [K{k} _ (by decide) (by decide), K{k}.acc (by decide) (by decide)]; exact v{k-1}_{d:x}")
                self.emit(f"  have l{k}_{d:x} : (n{k}.mem (B + 0x420 + BitVec.ofNat 32 (0x{d:X} + 0x30))).toNat ≤ 1 := by")
                self.emit(f"    rw [K{k} _ (by decide) (by decide)]; exact l{k-1}_{d:x}")
                newsv[d] = v
        for d, (v, proof, lproof) in sorted(written_sv.items()):
            self.emit(f"  have v{k}_{d:x} : sgnVal (n{k}.mem (B + 0x420 + BitVec.ofNat 32 (0x{d:X} + 0x30))).toNat")
            self.emit(f"      (accV n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12) = {v} := by")
            for line in proof:
                self.emit(f"    {line}")
            self.emit(f"  have l{k}_{d:x} : (n{k}.mem (B + 0x420 + BitVec.ofNat 32 (0x{d:X} + 0x30))).toNat ≤ 1 := by")
            for line in lproof:
                self.emit(f"    {line}")
            newsv[d] = v
        self.sv = newsv
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
                self.emit(f"  have w{k}_{e:x} : memLoad32 n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {lean_val(v)} := by")
                self.emit(f"    rw [← w{k-1}_{e:x}]; exact memLoad32_congr fun j hj => by")
                self.emit(f"      rw [add_ofNat_assoc]; exact K{k} _ (by omega) (by omega)")
                neww[e] = v
        for e, (v, proof) in sorted(written_words.items()):
            self.emit(f"  have w{k}_{e:x} : memLoad32 n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {lean_val(v)} := by")
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
            elif tk[0] == ".aluImm" and tk[1] == ".and":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3]))
                v = ("C", x[1] & int(tk[4], 16)) if x is not None and x[0] == "C" else None
            elif tk[0] == ".alu" and tk[1] == ".and":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3])); y = vals.get(reg_of(tk[4]))
                v = ("C", x[1] & y[1]) if x is not None and y is not None and x[0] == "C" and y[0] == "C" else None
            elif tk[0] == ".alu" and tk[1] == ".mul":
                rd = reg_of(tk[2]); x = vals.get(reg_of(tk[3])); y = vals.get(reg_of(tk[4]))
                v = ("C", (x[1] * y[1]) & 0xFFFFFFFF) if x is not None and y is not None and x[0] == "C" and y[0] == "C" else None
            elif tk[0] in (".aluImm", ".alu"):
                rd = reg_of(tk[2]); v = None
            else:
                raise ValueError(text)
            vals[rd] = v
            writes[rd] = v
            off += ln
        if writes_extra:
            writes.update(writes_extra)
        blk = f"pv{self.name}{start:x}"
        if all(b[0] != blk for b in self.blocks):
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

    def call(self, wrapper, off, args, c, w, written_acc=None, written_bytes=None, extra_regs=None, pre=None,
             written_sv=None, written_mbf=None, written_words=None):
        k = self.k = self.k + 1
        self.emit(f"  -- 0x{off:X}: {wrapper}")
        for line in pre or []:
            self.emit(f"  {line}")
        ev = f"E{k-1}{ENV_SUFFIX[(self.lvl, wrapper_level(wrapper))]}"
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
        self.mem_facts(k, c, w, written_acc, written_bytes, written_sv=written_sv, written_mbf=written_mbf,
                       written_words=written_words)
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

    def conclusion(self, off, extra=(), only=None):
        """The facts at the end, as a conjunction, and the term that proves it. `only`
        optionally names, per kind, the facts to keep."""
        only = only or {}
        keep = lambda kind, key: kind not in only or key in only[kind]
        k = self.k
        conj = [f"Steps n0 n'", f"St n'.mem PV n' 0x{off:X} (reg n')", f"{self.envt} n'.mem",
                "(∀ x, PvR B x → n'.mem x = n0.mem x)"]
        terms = [f"t{k}", f"s{k}", f"E{k}", f"fR{k}"]
        for r, v in sorted(self.regs.items()):
            if re.search(r"reg n[1-9]", lean_val(v)) or not keep("regs", r):
                continue
            conj.append(f"reg n' {rname(r)} = {lean_val(v)}"); terms.append(f"g{k}_{r}")
        for stmt, term in extra:
            conj.append(stmt); terms.append(term.format(k=k))
        for d, v in sorted(self.acc.items()):
            if not keep("acc", d):
                continue
            conj.append(f"accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12 = {v}"); terms.append(f"a{k}_{d:x}")
        for e, v in sorted(self.bytes.items()):
            conj.append(f"n'.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {v}"); terms.append(f"b{k}_{e:x}")
        for e, v in sorted(self.words.items()):
            if not keep("words", e):
                continue
            conj.append(f"memLoad32 n'.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {lean_val(v)}"); terms.append(f"w{k}_{e:x}")
        for d, v in sorted(self.sv.items()):
            if not keep("sv", d):
                continue
            conj.append(f"sgnVal (n'.mem (B + 0x420 + BitVec.ofNat 32 (0x{d:X} + 0x30))).toNat "
                        f"(accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12) = {v}"); terms.append(f"v{k}_{d:x}")
            conj.append(f"(n'.mem (B + 0x420 + BitVec.ofNat 32 (0x{d:X} + 0x30))).toNat ≤ 1"); terms.append(f"l{k}_{d:x}")
        for d, (N, kind, v) in sorted(self.mbf.items()):
            if not keep("mbf", d):
                continue
            conj.append(self.mbf_stmt(0, d, N, kind, v).replace("n0.mem", "n'.mem")); terms.append(f"mb{k}_{d:x}")
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
        k = g.k
        svs = {}
        for d, v in g.sv.items():
            if src <= d and d + 49 <= src + N:
                nd = dst + (d - src)
                o_ = d - src
                hb = [f"have hb := V{k + 1} (0x{o_:X} + 0x30) (by omega)",
                      f"rw [show 0x{dst:X} + (0x{o_:X} + 0x30) = 0x{nd:X} + 0x30 by omega,",
                      f"  show 0x{src:X} + (0x{o_:X} + 0x30) = 0x{d:X} + 0x30 by omega] at hb"]
                svs[nd] = (v, hb + [
                    f"rw [hb, accV_S (M := n{k}.mem) (d := 0x{d:X}) 12 fun q hq => by",
                    f"  have := V{k + 1} (0x{o_:X} + q) (by omega)",
                    f"  rwa [show 0x{dst:X} + (0x{o_:X} + q) = 0x{nd:X} + q by omega,",
                    f"    show 0x{src:X} + (0x{o_:X} + q) = 0x{d:X} + q by omega] at this]",
                    f"exact v{k}_{d:x}"], hb + [f"rw [hb]; exact l{k}_{d:x}"])
        words = {}
        for e, v in g.words.items():
            if src <= e and e + 4 <= src + N:
                ne = dst + (e - src)
                words[ne] = (v, [
                    f"rw [← w{k}_{e:x}]",
                    "exact memLoad32_cp fun q hq => by",
                    f"  have := V{k + 1} (0x{e - src:X} + q) (by omega)",
                    f"  rwa [show 0x{dst:X} + (0x{e - src:X} + q) = 0x{ne:X} + q by omega,",
                    f"    show 0x{src:X} + (0x{e - src:X} + q) = 0x{e:X} + q by omega] at this"])
        mbs = {}
        for d, (Nd, kind, v) in g.mbf.items():
            if src <= d and d + Nd <= src + N:
                nd = dst + (d - src)
                mbs[nd] = (Nd, kind, v, [
                    f"rw [memBytes_cp (M := n{k}.mem) (d := 0x{d:X}) fun q hq => by",
                    f"  have := V{k + 1} (0x{d - src:X} + q) (by omega)",
                    f"  rwa [show 0x{dst:X} + (0x{d - src:X} + q) = 0x{nd:X} + q by omega,",
                    f"    show 0x{src:X} + (0x{d - src:X} + q) = 0x{d:X} + q by omega] at this]",
                    f"exact mb{k}_{d:x}"])
        g.call("pv_mc", off, f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 (by decide) (by decide) (by decide)", dst, N,
               copy_facts(g, dst, src, N, f"V{k + 1}"), written_sv=svs, written_mbf=mbs, written_words=words)

    def mcK(self, off, dst, K, N, data):
        g = self.g
        k = g.k
        acc = {}
        for o in range(0, N - 47, 0x30):
            if o == 0:
                acc[dst] = (f"dataVal {data} 0 12", [
                    f"rw [show BitVec.ofNat 32 0x{K:X} = BitVec.ofNat 32 0x{K:X} + BitVec.ofNat 32 0 from (add_ofNat_zero _).symm] at V{k + 1}",
                    f"rw [accV_K 12 fun q hq => V{k + 1} q (by omega)]",
                    f"exact code_accV (d := {data}) {g.env(k)}.D2.{DATA_FIELD[data]} 0 12 (by decide)",
                ])
            else:
                acc[dst + o] = (f"dataVal {data} 0x{o:X} 12", [
                    f"rw [accV_KD (M := n{k}.mem) (K := BitVec.ofNat 32 0x{K:X}) (d := 0x{o:X}) 12 fun q hq => by",
                    f"  have := V{k + 1} (0x{o:X} + q) (by omega)",
                    f"  rwa [show 0x{dst:X} + (0x{o:X} + q) = 0x{dst + o:X} + q by omega] at this]",
                    f"exact code_accV (d := {data}) {g.env(k)}.D2.{DATA_FIELD[data]} 0x{o:X} 12 (by decide)",
                ])
        g.call("pv_mcK", off, f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 (by decide) (by decide) (by decide)", dst, N, acc)

    def smul(self, off, co, cx, cy, hB):
        """`ConstMontyForm::mul` of the limbs at `cx` and `cy`, with `hB` bounding the second."""
        g = self.g
        k = g.k
        val = f"n3fm ({g.acc[cx]}) ({g.acc[cy]})"
        acc = {co: (val, [f"rw [V{k + 1}, a{k}_{cx:x}, a{k}_{cy:x}]"])}
        g.call("pv_smul", off, f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 (by decide) (by decide) (by decide) (by decide) (by decide)\n"
               f"    (by decide) (by rw [a{k}_{cy:x}]; exact {hB})", co, 48, acc)

    def csel(self, off, dst, a, b):
        """Select with a choice of 0, so the limbs at offset `a`; `b` is a constant."""
        g = self.g
        acc = {dst: (g.acc[a], [f"rw [V{g.k + 1}, ite_eq_right (by decide), a{g.k}_{a:x}]"])}
        g.call("pv_csel", off,
               f"g{g.k}_2 g{g.k}_10 g{g.k}_11 g{g.k}_12 g{g.k}_13 (.inl (by decide)) (by decide)\n"
               f"    (pv_lowS F (k := 0x60) (by decide) (by decide) (by decide))\n"
               f"    (pv_lowK F (n := 48) (k := 0x60) (by decide) (by decide) (by decide)) (by decide)\n"
               f"    (by rw [pv_at F 0x{a:X} (by decide)]; have := F.hi; omega)", dst, 48, acc)

    def cselS(self, off, dst, a, b, c):
        """Select between the limbs at offsets `a` and `b` of the frame with the choice `c`."""
        g = self.g
        k = g.k
        src = b if c == 1 else a
        lemma = "ite_eq_left (by decide)" if c == 1 else "ite_eq_right (by decide)"
        acc = {dst: (g.acc[src], [f"rw [V{k + 1}, {lemma}, a{k}_{src:x}]"])} if src in g.acc else {}
        g.call("pv_csel", off,
               f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 g{k}_13 (by decide) (by decide)\n"
               f"    (pv_lowS F (k := 0x60) (by decide) (by decide) (by decide))\n"
               f"    (pv_lowS F (k := 0x60) (by decide) (by decide) (by decide)) (pv_al F (by decide) (by decide))\n"
               f"    (by rw [pv_at F 0x{a:X} (by decide)]; have := F.hi; omega)", dst, 48, acc)

    def sbr(self, off, base, imm, c):
        """A byte store from a register to offset `c` of the frame, tracking no value."""
        g = self.g
        k = g.k
        g.store("pv_sb", off, INSTR[off][1], f"(by rw [g{k}_{base}]; pv_addr) (by decide)", c, 1)

    def lbu(self, off, rd, base, e, val):
        """`lbu rd, 0(base)` of the byte at offset `e` of the frame, whose value is `val`."""
        g = self.g
        k = g.k = g.k + 1
        ln = INSTR[off][1]
        g.emit(f"  -- 0x{off:X}: lbu")
        g.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.lbu {g.env(k-1)}.C.self pv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
        g.emit(f"  have s{k} : St n{k}.mem PV n{k} 0x{off + ln:X} (reg n{k}) := ⟨u{k}.pc, rfl, fun _ => rfl⟩")
        g.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        g.emit(f"  have E{k} : {g.envt} n{k}.mem := by rw [m{k}]; exact E{k-1}")
        g.emit(f"  have fr{k} : ∀ x, PvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        g.emit(f"  have K{k} : PvKeep B n{k-1}.mem n{k}.mem 0 0 := fun e _ _ => by rw [m{k}]")
        g.common(k, f"(.single d{k})")
        new = {}
        for r, v in sorted(g.regs.items()):
            if r == rd:
                continue
            g.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [u{k}.regs, upd_ne (by decide) (by decide), g{k-1}_{r}]")
            new[r] = v
        g.emit(f"  have g{k}_{rd} : reg n{k} {rname(rd)} = {lean_val(val)} := by")
        g.emit(f"    rw [u{k}.regs]; simp +decide only [upd, ↓reduceIte]")
        g.emit(f"    rw [g{k-1}_{base}, show {lean_val(g.regs[base])} + 0x0 = B + 0x420 + BitVec.ofNat 32 0x{e:X} by pv_addr, b{k-1}_{e:x}]")
        new[rd] = val
        g.regs = new
        g.mem_facts(k, 0, 0)
        g.end_step()
        return k

    def norm(self, off, co, cx, cn, sx, fs, X, N):
        """`norm` of the value at `cx` (sign byte `sx`, magnitude `X`) with `f`'s sign `fs`."""
        g = self.g
        k = g.k
        val = f"normVal ({sx}).toNat ({fs}).toNat ({X}) ({N})"
        acc = {co: (val, [f"rw [V{k + 1}]",
                          f"show normVal (n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{cx + 0x30:X})).toNat _ _ _ = _",
                          f"rw [b{k}_{cx + 0x30:x}, g{k}_12, a{k}_{cx:x}, a{k}_{cn:x}]"])}
        g.call("pv_norm", off, f"g{k}_2 g{k}_10 g{k}_11 hfs g{k}_13 (by decide) (by decide) (by decide)\n"
               f"    (by decide) (by decide) (by decide)\n"
               f"    (by show (n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{cx + 0x30:X})).toNat ≤ 1; rw [b{k}_{cx + 0x30:x}]; exact hsx)",
               co, 48, acc,
               pre=[f"have hfs : reg n{k} a2 = 0 ∨ reg n{k} a2 = 1 := by rw [g{k}_12]; exact zext_01 hsf"])

    def eq(self, off, c):
        """`Uint<12>::eq` of the limbs at offset `c` against 1."""
        g = self.g
        k = g.k
        A = g.acc[c]
        g.regs_at_call_a1 = g.regs[11]
        g.call("pv_eq", off, f"g{k}_2 g{k}_10 g{k}_11 (by decide) (by decide) (by decide)", 0, 0,
               pre=[f"have keep_a{k + 1} := a{k}_{c:x}", f"have keep_u{k + 1} := {g.env(k)}.D2.u1"])
        k = g.k
        g.emit(f"  have keep_eq : reg n{k} a0 = (if {A} = 1 then 1 else 0) := by")
        g.emit(f"    rw [V{k}]")
        g.emit(f"    by_cases h : {A} = 1")
        Kv = lean_val(g.regs_at_call_a1)
        g.emit(f"    · rw [ite_eq_left h, ite_eq_left ((pv_eq_one (K := {Kv}) keep_u{k}).2 (by rw [keep_a{k}]; exact h))]")
        g.emit(f"    · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [← keep_a{k}]; exact (pv_eq_one (K := {Kv}) keep_u{k}).1 h'))]")

    def branch(self, off):
        """A branch on registers whose values are constants, taken or not as they decide."""
        g = self.g
        text, ln = INSTR[off]
        tk = tokens(text)
        op, r1, r2, imm = tk[1], reg_of(tk[2]), reg_of(tk[3]), int(tk[4], 16)
        v1 = C(0) if r1 == 0 else g.regs[r1]
        v2 = C(0) if r2 == 0 else g.regs[r2]
        assert v1[0] == "C" and v2[0] == "C", text
        a, b = v1[1], v2[1]
        taken = {".beq": a == b, ".bne": a != b, ".bltu": a < b, ".bgeu": a >= b,
                 ".blt": s32(a) < s32(b), ".bge": s32(a) >= s32(b)}[op]
        tgt = (off + s32(imm)) if taken else off + ln
        k = g.k = g.k + 1
        rws = [f"g{k-1}_{r}" for r in (r1, r2) if r != 0] + ([f"s{k-1}.zero"] if 0 in (r1, r2) else [])
        g.emit(f"  -- 0x{off:X}: branch, {'taken' if taken else 'not taken'}")
        g.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.{'taken' if taken else 'notTaken'} {g.env(k-1)}.C.self 0x{tgt:X} pv_at_{off:x}")
        g.emit(f"    (by decide) (by rw [{', '.join(rws)}]; decide)")
        g.emit(f"  have s{k} : St n{k}.mem PV n{k} 0x{tgt:X} (reg n{k}) := ⟨u{k}.pc, rfl, fun _ => rfl⟩")
        g.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        g.emit(f"  have E{k} : {g.envt} n{k}.mem := by rw [m{k}]; exact E{k-1}")
        g.emit(f"  have fr{k} : ∀ x, PvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        g.emit(f"  have K{k} : PvKeep B n{k-1}.mem n{k}.mem 0 0 := fun e _ _ => by rw [m{k}]")
        g.common(k, f"(.single d{k})")
        for r, v in sorted(g.regs.items()):
            g.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [u{k}.regs, g{k-1}_{r}]")
        g.mem_facts(k, 0, 0)
        g.end_step()
        return tgt

    def pt_bound(self, k, c, lt):
        return (f"(by rw [a{k}_{c:x}]; exact ({lt}).1)",
                f"(by show accV n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{c + 0x30:X}) 12 < p384; rw [a{k}_{c + 0x30:x}]; exact ({lt}).2.1)",
                f"(by show accV n{k}.mem (B + 0x420 + BitVec.ofNat 32 0x{c + 0x60:X}) 12 < p384; rw [a{k}_{c + 0x60:x}]; exact ({lt}).2.2)")

    def pt_facts(self, co, val, rws):
        g = self.g
        k = g.k
        acc = {}
        for j, proj in ((0, "1"), (0x30, "2.1"), (0x60, "2.2")):
            acc[co + j] = (f"({val}).{proj}", [
                f"have hv := V{k + 1}",
                "simp only [Nat.reduceAdd] at hv",
                f"rw [{', '.join(rws)}] at hv",
                f"exact congrArg (·.{proj}) hv"])
        return acc

    def pd(self, off, co, cx, P, lt):
        """The point doubling of the point `P` at `cx` (coordinates below `p` by `lt`), at `co`."""
        g = self.g
        k = g.k
        rws = [f"a{k}_{cx + j:x}" for j in (0, 0x30, 0x60)]
        acc = self.pt_facts(co, f"ptDblT ({P})", rws)
        b = self.pt_bound(k, cx, lt)
        g.call("pv_pd", off, f"g{k}_2 g{k}_10 g{k}_11 (by decide) (by decide) (by decide) (by decide)\n"
               f"    {b[0]}\n    {b[1]}\n    {b[2]}", co, 144, acc)

    def pa(self, off, cl, cr, R, ltl, ltr):
        """The point addition of the points at `cl` and `cr`, over `cl`; `R` names the sum."""
        g = self.g
        k = g.k
        rws = [f"a{k}_{c + j:x}" for c in (cl, cr) for j in (0, 0x30, 0x60)]
        acc = self.pt_facts(cl, R, rws)
        b1 = self.pt_bound(k, cl, ltl)
        b2 = self.pt_bound(k, cr, ltr)
        g.call("pv_pa", off, f"g{k}_2 g{k}_10 g{k}_11 (by decide) (by decide) (by decide) (by decide)\n"
               f"    {b1[0]}\n    {b1[1]}\n    {b1[2]}\n    {b2[0]}\n    {b2[1]}\n    {b2[2]}", cl, 144, acc)

    def za(self, off, c):
        g = self.g
        k = g.k
        g.call("pv_za", off, f"g{k}_2 g{k}_10 (by decide)", c, 48)

    def mr(self, off, co, cx, hX):
        g = self.g
        k = g.k
        acc = {co: (f"n3fm ({g.acc[cx]}) 1", [f"rw [V{k + 1}, a{k}_{cx:x}]"])}
        g.call("pv_mr", off, f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 g{k}_13 (by decide) (by decide) (by decide) (by decide)\n"
               f"    (by rw [a{k}_{cx:x}]; exact {hX})", co, 48, acc)

    def tbb(self, off, co, cx):
        g = self.g
        k = g.k
        mbs = {co: (48, "leNr", g.acc[cx], [f"rw [V{k + 1}, a{k}_{cx:x}]"])}
        g.call("pv_tbb", off, f"g{k}_2 g{k}_10 g{k}_11 (by decide) (by decide) (by decide)", co, 48, written_mbf=mbs)

    def rev(self, off, c):
        g = self.g
        k = g.k
        N, kind, v = g.mbf[c]
        assert kind == "leNr" and N == 48
        mbs = {c: (48, "leN", v, [f"rw [V{k + 1}]", f"exact mb{k}_{c:x}"])}
        g.call("pv_rev", off, f"g{k}_2 g{k}_10 g{k}_11 (by decide)", c, 48, written_mbf=mbs)

    def zloop(self, c, N):
        """The byte loop from 0x9F4 that zeroes `N` bytes at `c`, ending at 0x9FE."""
        g = self.g
        k = g.k = g.k + 1
        g.emit(f"  -- 0x9F4: zeroing loop")
        g.emit(f"  obtain ⟨n{k}, t{k}x, s{k}, fr{k}, K{k}, V{k}, rg{k}⟩ := pv_zl F (c := 0x{c:X}) 0x{N:X} 0 {g.env(k-1)} s{k-1}")
        g.emit(f"    g{k-1}_10 g{k-1}_11 (by decide) (by decide)")
        g.emit(f"  have E{k} : {g.envt} n{k}.mem := E{k-1}.fr F fr{k}")
        g.common(k, f"t{k}x")
        new = {}
        for r, v in sorted(g.regs.items()):
            if r in (10, 11):
                continue
            g.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [rg{k} {rname(r)} (by decide) (by decide), g{k-1}_{r}]")
            new[r] = v
        g.regs = new
        mbs = {c: (N, "list", f"List.replicate 0x{N:X} 0",
                   [f"exact memBytes_zero fun j hj => by have := V{k} j hj; rwa [Nat.add_zero] at this"])}
        g.mem_facts(k, c, N, written_mbf=mbs)
        g.end_step()

    def wf(self, off, cw, cc):
        g = self.g
        k = g.k
        X = g.mbf[cc][2]
        ds = f"wnafGo ({X}) 0x180 0x181 0 0"
        mbs = {cw: (0x181, "list", f"wnafBytes ({ds}) 0x181", [f"exact V{k + 1}.2"])}
        g.call("pv_wf", off, f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 g{k}_13 g{k}_14 (by decide) (by decide) (by decide)\n"
               f"    mb{k}_{cc:x} mb{k}_{cw:x}", cw, 0x181, written_mbf=mbs,
               extra_regs={10: (("U", f"BitVec.ofNat 32 ({ds}).length"), f"exact V{k + 1}.1")})

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
                written_words={c: (g.regs[src], [f"rw [V{k + 1}, g{k}_{src}]"])})

    def tq(self, ct):
        """Facts giving the matrix at `ct` from the words the stores left, before a call."""
        g = self.g
        k = g.k
        lines, vals = [], []
        for i, o_ in enumerate([0, 8, 0x10, 0x18]):
            addr = f"0x{ct:X}" if o_ == 0 else f"(0x{ct:X} + 0x{o_:X})"
            lo, hi = lean_val(g.words[ct + o_]), lean_val(g.words[ct + o_ + 4])
            vals.append(f"(i64Val (W64 ({lo}) ({hi})))")
            lines.append(f"have tq{k + 1}_{i} : accV n{k}.mem (B + 0x420 + BitVec.ofNat 32 {addr}) 2 = W64 ({lo}) ({hi}) := by")
            lines.append(f"  rw [accV2_S, show ({addr} + 4 : Nat) = 0x{ct + o_ + 4:X} from rfl" +
                         ("" if o_ == 0 else f", show ({addr} : Nat) = 0x{ct + o_:X} from rfl") +
                         f", w{k}_{ct + o_:x}, w{k}_{ct + o_ + 4:x}]")
        return lines, vals

    def ufg(self, off, co, ca, cb, ct, n):
        g = self.g
        k = g.k
        pre, (u, v, q, r) = self.tq(ct)
        F, G = g.sv[ca], g.sv[cb]
        val1 = f"fgUpd ({F}) ({G}) {u} {v} {n}"
        val2 = f"fgUpd ({F}) ({G}) {q} {r} {n}"
        dest = f"obtain ⟨h1, h2, h3, h4⟩ := V{k + 1}"
        rws = f"v{k}_{ca:x}, v{k}_{cb:x}, tq{k + 1}_0, tq{k + 1}_1, tq{k + 1}_2, tq{k + 1}_3"
        svs = {co: (val1, [dest, f"simp only [{rws}] at h1", "exact h1"], [dest, "exact h2"]),
               co + 0x34: (val2, [dest, f"simp only [{rws}] at h3",
                                  f"rw [show (0x{co:X} + 0x64 : Nat) = 0x{co + 0x34:X} + 0x30 from rfl,",
                                  f"  show (0x{co:X} + 0x34 : Nat) = 0x{co + 0x34:X} from rfl] at h3", "exact h3"],
                           [dest, f"rw [show (0x{co:X} + 0x64 : Nat) = 0x{co + 0x34:X} + 0x30 from rfl] at h4",
                            "exact h4"])}
        g.call("pv_ufg", off,
               f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 g{k}_13 g{k}_14 hn1 (by omega)\n"
               f"    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)\n"
               f"    (by decide) (by decide) (by decide) l{k}_{ca:x} l{k}_{cb:x}", co, 0x65, pre=pre, written_sv=svs)

    def ude(self, off, co, ca, cb, cm, ct, n, MI, Mv):
        g = self.g
        k = g.k
        pre, (u, v, q, r) = self.tq(ct)
        D, E = g.sv[ca], g.sv[cb]
        val1 = f"deUpd ({D}) ({E}) {u} {v} ({MI}) {n} ({Mv})"
        val2 = f"deUpd ({D}) ({E}) {q} {r} ({MI}) {n} ({Mv})"
        dest = f"obtain ⟨h1, h2, h3, h4⟩ := V{k + 1}"
        rws = f"v{k}_{ca:x}, v{k}_{cb:x}, tq{k + 1}_0, tq{k + 1}_1, tq{k + 1}_2, tq{k + 1}_3, a{k}_{cm:x}"
        svs = {co: (val1, [dest, f"simp only [{rws}] at h1", "exact h1"], [dest, "exact h2"]),
               co + 0x34: (val2, [dest, f"simp only [{rws}] at h3",
                                  f"rw [show (0x{co:X} + 0x64 : Nat) = 0x{co + 0x34:X} + 0x30 from rfl,",
                                  f"  show (0x{co:X} + 0x34 : Nat) = 0x{co + 0x34:X} from rfl] at h3", "exact h3"],
                           [dest, f"rw [show (0x{co:X} + 0x64 : Nat) = 0x{co + 0x34:X} + 0x30 from rfl] at h4",
                            "exact h4"])}
        g.call("pv_ude", off,
               f"g{k}_2 g{k}_10 g{k}_11 g{k}_12 g{k}_13 g{k}_14 g{k}_15 g{k}_16 g{k}_17 hn1 (by omega)\n"
               f"    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)\n"
               f"    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l{k}_{ca:x} l{k}_{cb:x}\n"
               f"    (by rw [a{k}_{cm:x}, ord_val]; decide)", co, 0x65, pre=pre, written_sv=svs)

    def lw(self, off, rd, base, imm, c):
        """`lw rd, imm(base)` reading the word at offset `c` of the frame."""
        g = self.g
        k = g.k = g.k + 1
        ln = INSTR[off][1]
        g.emit(f"  -- 0x{off:X}: lw")
        g.emit(f"  obtain ⟨n{k}, d{k}, u{k}⟩ := s{k-1}.lw {g.env(k-1)}.C.self pv_at_{off:x} (off' := 0x{off + ln:X}) (by decide)")
        g.emit(f"    (by rw [g{k-1}_{base}]; exact pv_al F (c := 0x{c:X}) (by decide) (by decide))")
        g.emit(f"  have s{k} : St n{k}.mem PV n{k} 0x{off + ln:X} (reg n{k}) := ⟨u{k}.pc, rfl, fun _ => rfl⟩")
        g.emit(f"  have m{k} : n{k}.mem = n{k-1}.mem := u{k}.mem")
        g.emit(f"  have E{k} : {g.envt} n{k}.mem := by rw [m{k}]; exact E{k-1}")
        g.emit(f"  have fr{k} : ∀ x, PvR B x → n{k}.mem x = n{k-1}.mem x := fun x _ => by rw [m{k}]")
        g.emit(f"  have K{k} : PvKeep B n{k-1}.mem n{k}.mem 0 0 := fun e _ _ => by rw [m{k}]")
        g.common(k, f"(.single d{k})")
        new = {}
        for r, v in sorted(g.regs.items()):
            if r == rd:
                continue
            g.emit(f"  have g{k}_{r} : reg n{k} {rname(r)} = {lean_val(v)} := by rw [u{k}.regs, upd_ne (by decide) (by decide), g{k-1}_{r}]")
            new[r] = v
        val = g.words[c]
        g.emit(f"  have g{k}_{rd} : reg n{k} {rname(rd)} = {lean_val(val)} := by")
        g.emit(f"    rw [u{k}.regs]; simp +decide only [upd, ↓reduceIte]")
        g.emit(f"    rw [g{k-1}_{base}, show {lean_val(g.regs[base])} + 0x{imm:X} = B + 0x420 + BitVec.ofNat 32 0x{c:X} by pv_addr, w{k-1}_{c:x}]")
        new[rd] = val
        g.regs = new
        g.mem_facts(k, 0, 0)
        g.end_step()
        return k

    def umin(self, off):
        g = self.g
        g.call("pv_umin", off, f"g{g.k}_2", 0, 0,
               extra_regs={10: (("U", "BitVec.ofNat 32 (min rem 62)"), f"rw [V{g.k + 1}, g{g.k}_10, umin_ofNat hrem]")})

    def low(self, off, c):
        g = self.g
        k = g.k
        g.call("pv_low", off, f"g{k}_2 g{k}_10 (by decide) (by decide) l{k}_{c:x}", 0, 0,
               pre=[f"have keep_l{k + 1} := l{k}_{c:x}", f"have keep_v{k + 1} := v{k}_{c:x}"])
        k = g.k
        g.emit(f"  have keep_low{k} : W64 (reg n{k} a0) (reg n{k} a1) = lowestI ({g.sv[c]}) :=")
        g.emit(f"    V{k}.trans (lowest_sv keep_l{k} keep_v{k})")
        # the registers now hold the call's results
        g.emit(f"  have g{k}_10 : reg n{k} a0 = reg n{k} a0 := rfl")
        g.emit(f"  have g{k}_11 : reg n{k} a1 = reg n{k} a1 := rfl")
        g.regs[10] = ("U", f"reg n{k} a0")
        g.regs[11] = ("U", f"reg n{k} a1")
        return k

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
        ps.append(f"(w0_{e:x} : memLoad32 n0.mem (B + 0x420 + BitVec.ofNat 32 0x{e:X}) = {lean_val(v)})")
    for d, v in sorted(g.sv.items()):
        ps.append(f"(v0_{d:x} : sgnVal (n0.mem (B + 0x420 + BitVec.ofNat 32 (0x{d:X} + 0x30))).toNat "
                  f"(accV n0.mem (B + 0x420 + BitVec.ofNat 32 0x{d:X}) 12) = {v})")
        ps.append(f"(l0_{d:x} : (n0.mem (B + 0x420 + BitVec.ofNat 32 (0x{d:X} + 0x30))).toNat ≤ 1)")
    for d, (N, kind, v) in sorted(g.mbf.items()):
        ps.append(f"(mb0_{d:x} : {g.mbf_stmt(0, d, N, kind, v)})")
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


def stage_ca():
    g = Gen("CA", env3=True)
    g.regs = {2: S(0), 19: ("U", "dhi"), 21: ("U", "dlo"), 23: ("U", "BitVec.ofNat 32 rem"), 26: C(0xB),
              20: C(0x177023BB), 22: C(0x912B9F76), 24: C(1)}
    for r in (3, 4):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {0x120: "QX", 0x150: "QY", 0x180: "QZ", 0x1B0: "RM", 0x1E0: "SM", 0x210: "ZM",
             0xE10: "dataVal p384OrderData 0 12", 0xE40: "dataVal p384ScalarR2Data 0 12"}
    g.words = {0xE70: C(0x177023BB), 0xE74: C(0x912B9F76)}
    g.sv = {0x1714: "Fv", 0xD50: "Gv", 0x270: "Dv", 0x17A4: "Ev"}
    params = params_of(g, 0x406)
    o = Ops(g)
    o.sw(0x406, 2, 0x54, 24, 0x54)
    g.block(0x408, 0x40A); o.umin(0x40A)
    g.block(0x412, 0x41C); kf = o.low(0x41C, 0x1714)
    g.block(0x424, 0x430); kg = o.low(0x430, 0xD50)
    g.block(0x438, 0x44A)
    info = {
        "end": 0x44A, "name": "pv_stCA", "title": "the start of a batch of the inversion of `s`",
        "doc": "From 0x406 to 0x44A: the batch's length, the low words of `f` and `g`, and the identity\nmatrix.",
        "thmdoc": "**The start of a batch**, from 0x406 to 0x44A.",
        "params": "{B : Word} {dlo dhi : Word} {rem QX QY QZ RM SM ZM : Nat} {Fv Gv Dv Ev : Int} "
                  + params + " (hrem : rem < 2 ^ 32)",
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl"]
                 + [f"have g0_{r} : reg n0 ({r} : Fin 32) = reg n0 ({r} : Fin 32) := rfl" for r in (3, 4)],
        "import": "C3BootProofs.Proofs.Pv384Lib2",
        "extra": [("W64 (reg n' (27 : Fin 32)) (reg n' (25 : Fin 32)) = lowestI Fv",
                   f"(by rw [g{{k}}_27, g{{k}}_25]; exact keep_low{kf})"),
                  ("W64 (reg n' a0) (reg n' a1) = lowestI Gv", f"(by rw [g{{k}}_10, g{{k}}_11]; exact keep_low{kg})")],
    }
    return g, info


def stage_c2a():
    g = Gen("C2a", env3=True)
    g.regs = {2: S(0), 24: C(1)}
    for r in (3, 4):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {0x120: "QX", 0x150: "QY", 0x180: "QZ", 0x1B0: "RM", 0x1E0: "SM", 0x210: "ZM",
             0xE10: "dataVal p384OrderData 0 12", 0x270: "Ad", 0x1714: "Af"}
    g.bytes = {0x2A0: "sd", 0x1744: "sf"}
    params = params_of(g, 0x628)
    o = Ops(g)
    g.block(0x628, 0x632)
    o.lbu(0x632, 12, 9, 0x1744, ("U", "sf.zeroExtend 32"))
    g.block(0x636, 0x648)
    o.norm(0x648, 0x1294, 0x270, 0xE10, "sd", "sf.zeroExtend 32", "Ad", "dataVal p384OrderData 0 12")
    g.block(0x650, 0x660)
    o.eq(0x660, 0x1714)
    info = {
        "end": 0x668, "name": "pv_stC2a", "title": "the end of the inversion of `s`",
        "doc": "From 0x628 to 0x668: `d` normalized by `f`'s sign, and whether `f` is 1.",
        "thmdoc": "**After the loop**, from 0x628 to 0x668.",
        "params": "{B : Word} {sd sf : BitVec 8} {QX QY QZ RM SM ZM Ad Af : Nat} "
                  + params + " (hsd : sd.toNat ≤ 1) (hsf : sf.toNat ≤ 1)",
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl",
                  "have hsx := hsd"]
                 + [f"have g0_{r} : reg n0 ({r} : Fin 32) = reg n0 ({r} : Fin 32) := rfl" for r in (3, 4)],
        "import": "C3BootProofs.Proofs.Pv384Lib2",
        "extra": [("reg n' a0 = (if Af = 1 then 1 else 0)", "keep_eq")],
        "only": {"regs": {2, 3, 4, 9, 24}, "acc": {0x120, 0x150, 0x180, 0x1B0, 0x1E0, 0x210, 0x1294}},
    }
    return g, info


def stage_c2b(ok):
    g = Gen(f"C2b{ok}", env3=True)
    g.regs = {2: S(0), 24: C(1), 10: C(ok), 9: S(0x1744)}
    for r in (3, 4):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {0x120: "QX", 0x150: "QY", 0x180: "QZ", 0x1B0: "RM", 0x1E0: "SM", 0x210: "ZM", 0x1294: "INV"}
    params = params_of(g, 0x668)
    o = Ops(g)
    g.block(0x668, 0x684); o.mc(0x684, 0x17A4, 0x1294, 0x30)
    g.block(0x68C, 0x68E); o.bb(0x68E, C(ok), "rw [V{k}, g{p}_10]; rfl")
    g.block(0x696, 0x698); o.sbr(0x698, 9, 0x90, 0x17D4)
    g.block(0x69C, 0x6AA); o.ms0(0x6AA, 0xE10, 0x30)
    g.block(0x6B2, 0x6D0); o.cselS(0x6D0, 0x1294, 0xE10, 0x17A4, ok)
    g.block(0x6D8, 0x6E0); o.sbr(0x6E0, 25, 0x544, 0x12C4)
    g.block(0x6E4, 0x6FC); o.ms0(0x6FC, 0x17A4, 0x30)
    g.block(0x704, 0x71E); o.cselS(0x71E, 0xE10, 0x17A4, 0x1294, ok)
    g.block(0x726, 0x728); o.sbr(0x728, 25, 0x514, 0x1294)
    info = {
        "end": 0x72C, "name": f"pv_stC2b{ok}", "title": f"the inverse of `s` {'chosen' if ok else 'refused'}",
        "doc": f"From 0x668 to 0x72C, when `f` {'is' if ok else 'is not'} 1: the inverse of `s`, or zero, at 0xE10.",
        "thmdoc": f"**The inverse {'chosen' if ok else 'refused'}**, from 0x668 to 0x72C.",
        "params": "{B : Word} {QX QY QZ RM SM ZM INV : Nat} " + params,
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl"]
                 + [f"have g0_{r} : reg n0 ({r} : Fin 32) = reg n0 ({r} : Fin 32) := rfl" for r in (3, 4)],
        "import": "C3BootProofs.Proofs.Pv384Lib2",
        "only": {"regs": {2, 3, 4, 9, 10, 18, 25}, "acc": {0x120, 0x150, 0x180, 0x1B0, 0x1E0, 0x210, 0xE10}},
    }
    return g, info


def stage_d():
    g = Gen("D", env4=True)
    g.regs = {2: S(0), 18: S(0x17A4), 25: S(0xD80)}
    for r in (3, 4):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {0x120: "QX", 0x150: "QY", 0x180: "QZ", 0x1B0: "RM", 0x1E0: "SM", 0x210: "ZM", 0xE10: "W"}
    params = params_of(g, 0x730)
    o = Ops(g)
    g.block(0x730, 0x73E); o.mc(0x73E, 0x240, 0xE10, 0x30)
    g.block(0x746, 0x752); o.smul(0x752, 0xEA0, 0x210, 0x240, "hW")
    g.block(0x75A, 0x766); o.smul(0x766, 0x1324, 0x1B0, 0x240, "hW")
    g.block(0x76E, 0x784); o.mcK(0x784, 0xE10, 0x3FCC4600, 0x90, "p384GData")
    g.block(0x78C, 0x79A); o.mc(0x79A, 0x1294, 0x120, 0x90)
    g.block(0x7A2, 0x7B0); o.mc(0x7B0, 0x270, 0xE10, 0xC0)
    g.block(0x7B8, 0x7C6); o.mc(0x7C6, 0x330, 0x1294, 0xC0)
    g.block(0x7CE, 0x7DC); o.mc(0x7DC, 0x17A4, 0x270, 0x180)
    info = {
        "end": 0x7E4, "name": "pv_stD", "title": "`u₁` and `u₂`, and the pairs of the linear combination",
        "doc": "From 0x730 to 0x7E4: `u₁ = z·w` and `u₂ = r·w` in Montgomery form, and the pairs `(G, u₁)` and "
               "`(Q, u₂)` at 0x17A4.",
        "thmdoc": "**`u₁`, `u₂`, and the pairs**, from 0x730 to 0x7E4.",
        "params": "{B : Word} {QX QY QZ RM SM ZM W : Nat} " + params + " (hW : W < n384)",
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl"]
                 + [f"have g0_{r} : reg n0 ({r} : Fin 32) = reg n0 ({r} : Fin 32) := rfl" for r in (3, 4)],
        "import": "C3BootProofs.Proofs.Pv384Lib3",
        "only": {"regs": {2, 3, 4, 18, 23, 25},
                 "acc": {0x120, 0x150, 0x180, 0x1B0, 0x1E0, 0x210, 0x17A4, 0x17D4, 0x1804, 0x1834, 0x1864, 0x1894,
                         0x18C4, 0x18F4, 0x270, 0x2A0, 0x2D0, 0x300, 0x330, 0x360, 0x390, 0x3C0}},
    }
    return g, info


def pt_acc(c, P):
    return {c: f"({P}).1", c + 0x30: f"({P}).2.1", c + 0x60: f"({P}).2.2"}


def stage_e(i):
    """One pass of the table loop, for pair `i`."""
    g = Gen(f"E{i}", env4=True)
    P = f"(P{i}X, P{i}Y, P{i}Z)"
    lt = f"hP{i}"
    g.regs = {2: S(0), 18: S(0x17A4 + 0xC0 * i), 19: C(i), 20: C(2), 21: C(0x480), 22: S(0x450), 23: C(0x3FCC4600),
              25: S(0xD80)}
    for r in (3, 4):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {0x120: "QX", 0x150: "QY", 0x180: "QZ", 0x1B0: "RM", 0x1E0: "SM", 0x210: "ZM",
             0x1834: "U1", 0x18F4: "U2"}
    g.acc.update(pt_acc(0x17A4, "(P0X, P0Y, P0Z)"))
    g.acc.update(pt_acc(0x1864, "(P1X, P1Y, P1Z)"))
    g.acc.update(pt_acc(0x270, "(P0X, P0Y, P0Z)"))
    g.acc.update(pt_acc(0x330, "(P1X, P1Y, P1Z)"))
    g.acc.update({0x300: "U1", 0x3C0: "U2"})
    if i == 1:
        for j in range(8):
            g.acc.update(pt_acc(0x450 + 0x90 * j, f"tblPt (P0X, P0Y, P0Z) {j}"))
    start = 0x7F4
    if i == 0:
        g.regs = {r: v for r, v in g.regs.items() if r not in (19, 20, 21, 22)}
        start = 0x7E4
    params = params_of(g, start)
    o = Ops(g)
    if i == 0:
        g.block(0x7E4, 0x7F0)
        o.branch(0x7F0)
    g.block(0x7F4, 0x802); o.mc(0x802, 0xD50, 0x17A4 + 0xC0 * i, 0xC0)
    g.block(0x80A, 0x816); o.branch(0x816)
    for j in range(8):
        g.block(0x818, 0x820); o.mcK(0x820, 0x1294 + 0x90 * j, 0x3FCC4600, 0x90, "p384GData")
        g.block(0x828, 0x82E); o.branch(0x82E)
    g.block(0x830, 0x850); o.mc(0x850, 0xE10, 0x1294, 0x480)
    g.block(0x858, 0x868); o.pd(0x868, 0x1714, 0xD50, P, lt)
    g.block(0x870, 0x884); o.mc(0x884, 0x1294, 0xD50, 0x90)
    o.branch(0x88C)
    for j in range(8):
        g.block(0x88E, 0x89E); o.mc(0x89E, 0xE10 + 0x90 * j, 0x1294, 0x90)
        g.block(0x8A6, 0x8B6)
        o.pa(0x8B6, 0x1294, 0x1714, f"tblPt {P} {j + 1}", f"tblPt_lt {lt} {j}", f"ptDblT_lt {P}")
        g.block(0x8BE, 0x8C6); o.branch(0x8C6)
    g.block(0x8C8, 0x8E0); o.mc(0x8E0, 0x1294, 0xE10, 0x480)
    g.block(0x8E8, 0x8FA); o.mc(0x8FA, 0x450 + 0x480 * i, 0x1294, 0x480)
    g.block(0x902, 0x904); end = o.branch(0x904)
    keep = {0x120, 0x150, 0x180, 0x1B0, 0x1E0, 0x210, 0x1834, 0x18F4, 0x300, 0x3C0}
    keep |= {0x17A4 + j for j in (0, 0x30, 0x60)} | {0x1864 + j for j in (0, 0x30, 0x60)}
    keep |= {0x270 + j for j in (0, 0x30, 0x60)} | {0x330 + j for j in (0, 0x30, 0x60)}
    keep |= {0x450 + 0x90 * j + c for j in range(8 * (i + 1)) for c in (0, 0x30, 0x60)}
    pts = "{P0X P0Y P0Z P1X P1Y P1Z : Nat}"
    info = {
        "end": end, "name": f"pv_stE{i}", "title": f"the table of pair {i}",
        "doc": f"One pass of the table loop: the odd multiples `P + j·2P` of pair {i}'s point, at "
               f"0x{0x450 + 0x480 * i:X}.",
        "thmdoc": f"**The table of pair {i}**, from 0x{start:X} to 0x{end:X}.",
        "params": "{B : Word} {QX QY QZ RM SM ZM U1 U2 : Nat} " + pts + " " + params
                  + f" (hP{i} : PtLt {P})",
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl"]
                 + [f"have g0_{r} : reg n0 ({r} : Fin 32) = reg n0 ({r} : Fin 32) := rfl" for r in (3, 4)],
        "import": "C3BootProofs.Proofs.Pv384Lib3",
        "only": {"regs": {2, 3, 4, 18, 19, 20, 21, 22, 23, 25}, "acc": keep},
    }
    return g, info


def stage_f(i):
    """One pass of the wNAF loop, for pair `i`."""
    g = Gen(f"F{i}", env4=True)
    g.lvl = 5
    g.envt = "PvEnv5"
    g.regs = {2: S(0), 25: S(0xD80)}
    if i == 1:
        g.regs.update({9: C(1), 18: C(0x3FCC4D28), 19: S(0x1298), 20: C(0xE88FDC45), 21: S(0x17A4 + 0xC0),
                       22: C(2), 23: C(0x188), 24: S(0x1924)})
    for r in (3, 4):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {0x120: "QX", 0x150: "QY", 0x180: "QZ", 0x1B0: "RM", 0x1E0: "SM", 0x210: "ZM",
             0x1834: "U1", 0x18F4: "U2", 0x300: "U1", 0x3C0: "U2"}
    for c, P in ((0x17A4, "(P0X, P0Y, P0Z)"), (0x1864, "(P1X, P1Y, P1Z)"), (0x270, "(P0X, P0Y, P0Z)"),
                 (0x330, "(P1X, P1Y, P1Z)")):
        g.acc.update(pt_acc(c, P))
    for t, P in ((0, "(P0X, P0Y, P0Z)"), (1, "(P1X, P1Y, P1Z)")):
        for j in range(8):
            g.acc.update(pt_acc(0x450 + 0x480 * t + 0x90 * j, f"tblPt {P} {j}"))
    if i == 1:
        ds0 = "wnafGo (n3fm U1 1) 0x180 0x181 0 0"
        g.words = {0x1924: ("U", f"BitVec.ofNat 32 ({ds0}).length")}
        g.mbf = {0x1928: (0x181, "list", f"wnafBytes ({ds0}) 0x181")}
    start = 0x908 if i == 0 else 0x958
    params = params_of(g, start)
    o = Ops(g)
    if i == 0:
        g.block(0x908, 0x920); o.mc(0x920, 0x17A4, 0x270, 0x180)
        g.block(0x928, 0x954); o.branch(0x954)
    hU = f"hU{i + 1}"
    g.block(0x958, 0x964); o.za(0x964, 0xD50)
    g.block(0x96C, 0x97A); o.mr(0x97A, 0xE10, 0x1834 + 0xC0 * i, hU)
    g.block(0x982, 0x992); o.tbb(0x992, 0xD50, 0xE10)
    g.block(0x99A, 0x9AE); o.mc(0x9AE, 0xE10, 0xD50, 0x30)
    g.block(0x9B6, 0x9C2); o.rev(0x9C2, 0xE10)
    g.block(0x9CA, 0x9DE); o.mc(0x9DE, 0xD50, 0xE10, 0x30)
    g.block(0x9E6, 0x9F2); o.branch(0x9F2); o.zloop(0xE10, 0x181)
    g.block(0x9FE, 0xA10); o.mc(0xA10, 0x1298, 0xE10, 0x181)
    g.block(0xA18, 0xA2E); o.wf(0xA2E, 0x1298, 0xD50)
    o.sw(0xA36, 25, 0x514, 10, 0x1294)
    g.block(0xA3A, 0xA4E); o.mc(0xA4E, 0xE10, 0x1294, 0x188)
    g.block(0xA56, 0xA68); o.mc(0xA68, 0x1924 + 0x188 * i, 0xE10, 0x188)
    g.block(0xA70, 0xA72); end = o.branch(0xA72)
    keep = {0x120, 0x150, 0x180, 0x1B0, 0x1E0, 0x210}
    keep |= {0x450 + 0x90 * j + c for j in range(16) for c in (0, 0x30, 0x60)}
    keep_pairs = {0x1834, 0x18F4, 0x300, 0x3C0} | {c + j for c in (0x17A4, 0x1864, 0x270, 0x330) for j in (0, 0x30, 0x60)}
    if i == 0:
        keep |= keep_pairs
    pts = "{P0X P0Y P0Z P1X P1Y P1Z : Nat}"
    info = {
        "end": end, "name": f"pv_stF{i}", "title": f"the wNAF digits of pair {i}",
        "doc": f"One pass of the wNAF loop: the digits of pair {i}'s scalar, out of Montgomery form, at "
               f"0x{0x1928 + 0x188 * i:X} with their count at 0x{0x1924 + 0x188 * i:X}.",
        "thmdoc": f"**The wNAF digits of pair {i}**, from 0x{start:X} to 0x{end:X}.",
        "params": "{B : Word} {QX QY QZ RM SM ZM U1 U2 : Nat} " + pts + " " + params + f" ({hU} : U{i + 1} < n384)",
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl"]
                 + [f"have g0_{r} : reg n0 ({r} : Fin 32) = reg n0 ({r} : Fin 32) := rfl" for r in (3, 4)],
        "import": "C3BootProofs.Proofs.Pv384Lib4",
        "only": {"regs": {2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25}, "acc": keep},
    }
    return g, info


def stage_cb():
    g = Gen("CB", env3=True)
    g.regs = {2: S(0), 19: ("U", "dhi"), 21: ("U", "dlo"), 23: ("U", "BitVec.ofNat 32 rem"), 26: C(0xB),
              20: C(0x177023BB), 22: C(0x912B9F76), 18: ("U", "BitVec.ofNat 32 n"),
              9: ("U", "ulo"), 17: ("U", "uhi"), 12: ("U", "vlo"), 16: ("U", "vhi"), 24: ("U", "qlo"),
              7: ("U", "qhi"), 30: ("U", "rlo"), 6: ("U", "rhi")}
    for r in (3, 4):
        g.regs[r] = ("U", f"reg n0 ({r} : Fin 32)")
    g.acc = {0x120: "QX", 0x150: "QY", 0x180: "QZ", 0x1B0: "RM", 0x1E0: "SM", 0x210: "ZM",
             0xE10: "dataVal p384OrderData 0 12", 0xE40: "dataVal p384ScalarR2Data 0 12"}
    g.words = {0x54: C(1), 0xE70: C(0x177023BB), 0xE74: C(0x912B9F76)}
    g.sv = {0x1714: "Fv", 0xD50: "Gv", 0x270: "Dv", 0x17A4: "Ev"}
    params = params_of(g, 0x530)
    o = Ops(g)
    g.block(0x530, 0x538)
    for i, (off, src) in enumerate([(0x538, 9), (0x53C, 17), (0x540, 12), (0x544, 16), (0x548, 24), (0x54C, 7),
                                    (0x550, 30), (0x554, 6)]):
        o.sw(off, 10, 0x524 + 4 * i, src, 0x1C68 + 4 * i)
    g.block(0x558, 0x57A); o.ufg(0x57A, 0x1294, 0x1714, 0xD50, 0x1C68, "n")
    g.block(0x582, 0x596); o.mc(0x596, 0x1714, 0x1294, 0x34)
    g.block(0x59E, 0x5B2); o.mc(0x5B2, 0xD50, 0x12C8, 0x34)
    MI = "(BitVec.ofNat 32 0x177023BB).toNat + 2 ^ 32 * (BitVec.ofNat 32 0x912B9F76).toNat"
    g.block(0x5BA, 0x5E4); o.ude(0x5E4, 0x1294, 0x270, 0x17A4, 0xE10, 0x1C68, "n", MI, "dataVal p384OrderData 0 12")
    g.block(0x5EC, 0x5FA); o.mc(0x5FA, 0x270, 0x1294, 0x34)
    g.block(0x602, 0x616); o.mc(0x616, 0x17A4, 0x12C8, 0x34)
    g.block(0x61E, 0x622, {23: ("U", "BitVec.ofNat 32 rem - BitVec.ofNat 32 n")})
    o.lw(0x622, 24, 2, 0x54, 0x54)
    info = {
        "end": 0x624, "name": "pv_stCB", "title": "the end of a batch of the inversion of `s`",
        "doc": "From 0x530 to 0x624: store the batch's matrix, apply it to `f`, `g`, `d`, and `e`,\nand count down the steps left.",
        "thmdoc": "**The end of a batch**, from 0x530 to 0x624.",
        "params": "{B : Word} {dlo dhi ulo uhi vlo vhi qlo qhi rlo rhi : Word} {rem n QX QY QZ RM SM ZM : Nat} {Fv Gv Dv Ev : Int} "
                  + params + " (hn1 : 1 ≤ n) (hn2 : n ≤ 62)",
        "intro": ["have t0 : Steps n0 n0 := .refl n0", "have fR0 : ∀ x, PvR B x → n0.mem x = n0.mem x := fun _ _ => rfl"]
                 + [f"have g0_{r} : reg n0 ({r} : Fin 32) = reg n0 ({r} : Fin 32) := rfl" for r in (3, 4)],
        "import": "C3BootProofs.Proofs.Pv384Lib2",
        "only": {"regs": {2, 3, 4, 19, 20, 21, 22, 23, 24, 26}, "words": {0xE70, 0xE74},
                 "sv": {0x270, 0xD50, 0x1714, 0x17A4}},
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
    g, info = {"B": stage_b, "C0": stage_c0, "CA": stage_ca, "CB": stage_cb, "C2a": stage_c2a,
               "C2b1": lambda: stage_c2b(1), "C2b0": lambda: stage_c2b(0), "D": stage_d,
               "E0": lambda: stage_e(0), "E1": lambda: stage_e(1), "F0": lambda: stage_f(0),
               "F1": lambda: stage_f(1)}[stage]()
    stmt, proof = g.conclusion(info["end"], info.get("extra", ()), info.get("only"))
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
