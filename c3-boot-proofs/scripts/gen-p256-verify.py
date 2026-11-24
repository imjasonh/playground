#!/usr/bin/env python3
"""Generates the stage proofs of `c3_crypto::p256_verify_prehash`.

Usage, from c3-boot-proofs/:
    python3 scripts/gen-p256-verify.py STAGE > C3BootProofs/Proofs/P2v<STAGE>.lean
    python3 scripts/gen-p256-verify.py --list

The stages run the engine of `gen-sigstore-verify.py`, which proved the same
check when `sigstore::verify` inlined it, on `p256VerifyPrehashCode`. The
function's frame base is `B + 0x21A0`, as in `sigstore::verify`, so the
engine's frame addresses carry over; its names are renamed from `Sv` to `P2v`
on output.
"""

import contextlib
import importlib.util
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("gsv", os.path.join(HERE, "gen-sigstore-verify.py"))
gsv = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gsv)

gsv.INSTR.clear()
for mm in re.finditer(
    r"theorem p2v_at_([0-9a-f]+) : fetchRel p256VerifyPrehashCode 0x[0-9A-F]+ = some \((.*), (\d+)\) :=",
    open("C3BootProofs/Proofs/P2vAt.lean").read(),
):
    gsv.INSTR[int(mm.group(1), 16)] = (mm.group(2), int(mm.group(3)))

KEEP = {"svConst", "svConstAddress", "SvP256Facts"}


def port(text):
    """Renames the engine's `sigstore::verify` names to this function's."""
    text = text.replace("sigstoreVerifyCode", "p256VerifyPrehashCode")
    text = re.sub(r"\bSV\b", "P2V", text)
    text = text.replace("gsVal_sv ", "gsVal_p2v ").replace("codeIn_sv ", "codeIn_p2v ")

    def ident(m):
        w = m.group(0)
        if w in KEEP:
            return w
        if w.startswith("sv_"):
            return "p2v_" + w[3:]
        if w.startswith("sv"):
            return "p2v" + w[2:]
        return "P2v" + w[2:]
    text = re.sub(r"(?<![\w'])(?:sv_\w+|sv[A-Z]\w*|Sv[A-Z0-9]\w*)", ident, text)
    return re.sub(r"\.sv\b", ".p2v", text)


class Gen(gsv.Gen):
    def fail(self, why_not, exit_lemma="p2v_fail"):
        """Closes a failing case at 0x142, with `p2v_fail0` at 0x144 with 0
        in `a0`, or with `p2v_panic_10c8` at the panic at 0x10C8."""
        k = self.k
        if exit_lemma == "p2v_panic_10c8":
            self.emit(f"  exact .inl ⟨({why_not}), Panics.of_steps t{k} (p2v_panic_10c8 F E{k} s{k} g{k}_2)⟩")
            return
        extra = f" g{k}_10" if exit_lemma == "p2v_fail0" else ""
        self.emit(f"  exact .inl ⟨({why_not}), {exit_lemma} F E{k} s{k} t{k} "
                  f"(fun x hx => (fR{k} x hx).trans (fM x hx).symm) V{k} hret g{k}_2 g{k}_3 g{k}_4{extra}⟩")

    def isrP(self, off, inp, y, post=None):
        """`ecdsa::in_scalar_range` of the 32 bytes at `a0`, outside the
        stack (`inp`), and at `y`."""
        k = self.k + 1
        return self.pure(off, "p2v_isrP", "", f"E{k-1} (EC0.p2v F fR{k-1}) s{k-1} p2v_at_{off:x} p2v_at_{off + 4:x} "
                         f"(by decide) (by decide) g{k-1}_10 g{k-1}_11 g{k-1}_12 g{k-1}_13", post)

    def sf2P(self, off, co, inp, post=None):
        """`ScalarValue::<NistP256>::from_slice` of the 32 bytes at `a1`,
        outside the stack (`inp`), into offset `co`; returns k. The caller
        splits."""
        k = self.k = self.k + 1
        self.call_head(k, off, "p2v_sf2P", f"(co := 0x{co:X})",
                       [f"c{k}", f"s{k}", f"sp{k}", f"rk{k}", f"L{k}", f"G{k}", f"K{k}", f"fr{k}"])
        self.emit(f"    F E{k-1} (BG0.p2v F fR{k-1}) s{k-1} p2v_at_{off:x} p2v_at_{off + 4:x} (by decide) (by decide) g{k-1}_2")
        self.emit(f"    {self.reg_is(k - 1, 10, co)} g{k-1}_11 (by decide) (by decide) {inp}")
        self.emit(f"  rw [p2v_mb fR{k-1} {inp}] at L{k} G{k}")
        for line in (post(k) if post else []):
            self.emit(line)
        self.common(k, f"c{k}", f"fr{k}", f"V{k-1}.keepL K{k} (by decide)")
        self.keep_regs(k, [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
                       lambda r: f"rk{k} {gsv.rname(r)} (by decide)")
        self.emit(f"  have g{k}_2 : reg n{k} sp = B + 0x21A0 := sp{k}")
        self.regs[2] = ("S", 0)
        return k

    def zloop(self, c, N):
        """The clearing loop at 0x908 over the `N` bytes at offset `c`."""
        n = len(self.out)
        super().zloop(c, N)
        self.out[n:] = [ln.replace("ec_zloop", "p2v_zloop").replace("0x184E", "0x908").replace("0x1858", "0x912")
                        for ln in self.out[n:]]

    def clone(self):
        c = super().clone()
        c.__class__ = Gen
        return c


def finish(g, off, keep_regs, keep_words=None, keep_bytes=None):
    stmt, proof = gsv.finish(g, off, keep_regs, keep_words, keep_bytes)
    return stmt.replace("SvErrRet B out v n0", "P2vRet B v n0 0"), proof


def start(g, regs, words):
    params = gsv.start(g, regs, words, {})
    return params


ORD256 = "BitVec.ofNat 32 (img% p256OrderBeAddress)"
IN_REGS = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"),
           8: ("U", "rp"), 9: ("U", "pk"), 19: ("U", "dg"), 20: ("U", "sq")}
IN_PARAMS = ["(r_in : P2vIn B rp 32)", "(s_in : P2vIn B sq 32)", "(k_in : P2vIn B pk 0x41)",
             "(dg_in : P2vIn B dg 32)", "(EC0 : P2vEcCode M0)"]
EC_BINDERS = "{B pk dg rp sq : Word} {v : Nat → Word} {n0 : Machine}"


def stage_a1():
    """From 0x48 to 0x8E: `r` and `s` are in `[1, n)`, and the key's
    encoding starts with 4."""
    g = Gen("A1")
    g.generic_alu = True
    params = start(g, IN_REGS, {}) + IN_PARAMS
    for b0, call, inp, L, hn in ((0x48, 0x5A, "r_in", "rp", "hr"), (0x64, 0x76, "s_in", "sq", "hs")):
        g.block(b0, call)
        k = g.isrP(call, inp, ORD256, lambda k, inp=inp: [
            f"  rw [p2v_mb fR{k-1} {inp}, mb_dataR F fR{k-1} (by decide) (by decide)] at a0_{k}"])
        prop = f"inScalarRange (memBytes M0 {L} 32) (memBytes M0 ({ORD256}) 32) = true"
        if call == 0x5A:
            def out(sub, k=k, hn=hn):
                sub.set_a0(k, 0, f"ite_eq_right {hn}")
                sub.branch(0x62, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
                sub.fail(sub.fail_proof(("prop", hn)), "p2v_fail0")
            g.prop_check(prop, hn, out)
            g.set_a0(k, 1, f"ite_eq_left {hn}")
            g.branch(0x62, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        else:
            def out(sub, k=k, hn=hn):
                sub.set_a0(k, 0, f"ite_eq_right {hn}")
                sub.block(0x7E, 0x82)
                sub.branch(0x82, True, f"by rw [g{sub.k}_11, s{sub.k}.zero]; decide")
                sub.fail(sub.fail_proof(("prop", hn)), "p2v_fail0")
            g.prop_check(prop, hn, out)
            g.set_a0(k, 1, f"ite_eq_left {hn}")
            g.block(0x7E, 0x82)
            g.branch(0x82, False, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
    g.load_in(0x84, "k_in", "(by decide)")
    g.block(0x88, 0x8A)

    def tag(sub):
        sub.branch(0x8A, True, f"by rw [g{sub.k}_11, g{sub.k}_12]; exact br_bne_t fun e => htag ((zext_eq4 _).mp e)")
        sub.fail(sub.fail_proof(("prop", "htag")), "p2v_fail0")
    g.prop_check("M0 pk = 4", "htag", tag)
    g.branch(0x8A, False, f"by rw [g{g.k}_11, g{g.k}_12, htag]; decide")
    stmt, proof = finish(g, 0x8E, [2, 3, 4, 8, 9, 19, 20], set(), set())
    info = {"name": "p2v_a1", "title": "the signature's scalars and the key's tag",
            "doc": "From 0x48 to 0x8E: the signature's `r` and `s` are in `[1, n)` for P-256's order `n`, "
            "and the key's SEC1 encoding starts with 4, an uncompressed point.",
            "params": params, "stmt": stmt, "proof": proof, "binders": EC_BINDERS, "start": 0x48,
            "import": "C3BootProofs.Proofs.P2vEc"}
    return g, info


def stage_a2():
    """From 0x8E to 0x186: the key decoded to a point, and `r` and `s` as
    scalars, both nonzero."""
    g = Gen("A2")
    g.generic_alu = True
    params = start(g, IN_REGS, {}) + IN_PARAMS + ["(D0 : P2Data M0)", "(BG0 : BGEnv M0)"]
    g.block(0x8E, 0x92)
    k = g.gsf(0x92, 0x98, "k_in")

    def bad_key(sub):
        sub.emit(f"  have z{k} := Er{k} hgs")
        sub.frame_after(k, [(0x98, 0x48)], {0x98: ("1", f"z{k}")})
        sub.load(0x9A, "lw")
        sub.branch(0x9C, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
        sub.fail(sub.fail_proof(("prop", "hgs")))
    g.prop_check("GsOk M0 pk", "hgs", bad_key)
    X, Y = "gsVal M0 pk 1 * 2 ^ 256 % p256", "gsVal M0 pk 0x21 * 2 ^ 256 % p256"
    g.emit(f"  obtain ⟨o1_{k}, o2_{k}, o3_{k}, o4_{k}⟩ := Ok{k} hgs")
    g.frame_after(k, [(0x98, 0x48)], {0x98: ("0", f"o1_{k}")}, {0xDC: ("(0 : BitVec 8)", f"o4_{k}")},
                  {0x9C: (8, X, f"o2_{k}"), 0xBC: (8, Y, f"o3_{k}")})
    g.load(0x9A, "lw")
    g.branch(0x9C, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    g.block(0x9E, 0xAE)
    g.mc(0xAE, 0x58, 0x9C, 0x40)
    g.load(0xB6, "lbu")
    for (b0, b1, inp, L, lw, br, mcb, mcoff, dst, hn) in (
            (0xBA, 0xC4, "r_in", "rp", 0xCC, 0xD0, 0xD2, 0xE0, 0x200, "hlr"),
            (0xE8, 0xF2, "s_in", "sq", 0xFA, 0xFE, 0x100, 0x114, 0xFE4, "hls")):
        g.block(b0, b1)
        k = g.sf2P(b1, 0xC80, inp)
        prop = f"beNat (memBytes M0 {L} 32) < C3.p256.n"

        def big(sub, k=k, lw=lw, br=br, hn=hn):
            sub.emit(f"  have z{k} := G{k} (Nat.le_of_not_lt {hn})")
            sub.frame_after(k, [(0xC80, 36)], {0xC80: ("1", f"z{k}")})
            sub.load(lw, "lw")
            sub.branch(br, True, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
            sub.fail(sub.fail_proof(("prop", hn)))
        g.prop_check(prop, hn, big)
        g.emit(f"  obtain ⟨z{k}, y{k}⟩ := L{k} {hn}")
        g.frame_after(k, [(0xC80, 36)], {0xC80: ("0", f"z{k}")}, {},
                      {0xC84: (8, f"beNat (memBytes M0 {L} 32)",
                               f"by rw [show B + 0x21A0 + BitVec.ofNat 32 0xC84 = B + 0x21A0 + BitVec.ofNat 32 0xC80 + 4 by sv_addr]; exact y{k}")})
        g.load(lw, "lw")
        g.branch(br, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
        g.block(mcb, mcoff)
        g.mc(mcoff, dst, 0xC84, 0x20)
    for (b0, b1, c, br, L, hn) in ((0x11C, 0x11E, 0x200, 0x12A, "rp", "hzr"),
                                   (0x12C, 0x134, 0xFE4, 0x140, "sq", "hzs")):
        g.block(b0, b1)
        k = g.sz(b1, c, lambda k, c=c: [f"  simp only [limbs0_iff a{k-1}_{c:x}] at a0_{k}"])
        prop = f"beNat (memBytes M0 {L} 32) ≠ 0"
        first = c == 0x200

        def zero(sub, k=k, b1=b1, br=br, hn=hn, first=first):
            sub.set_a0(k, 1, f"ite_eq_left (Decidable.of_not_not {hn})")
            sub.block(b1 + 8, br)
            sub.branch(br, first, f"by rw [g{sub.k}_10, s{sub.k}.zero]; decide")
            sub.fail(sub.fail_proof(("prop", hn)))
        g.prop_check(prop, hn, zero)
        g.set_a0(k, 0, f"ite_eq_right {hn}")
        g.block(b1 + 8, br)
        g.branch(br, not first, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    stmt, proof = finish(g, 0x186, [2, 3, 4, 18, 19, 26], set(), set())
    info = {"name": "p2v_a2", "title": "the key's point and the signature's scalars",
            "doc": "From 0x8E to 0x186: the key decodes to a point on P-256, and the signature's `r` and `s` "
            "are scalars below the order and not zero.",
            "params": params, "stmt": stmt, "proof": proof, "binders": EC_BINDERS, "start": 0x8E,
            "import": "C3BootProofs.Proofs.P2vEc"}
    return g, info


def stage_a3():
    """From 0x186 to the inversion's head at 0x3E0: the key's point in
    projective form, `r` and `s` as nonzero scalars, and the prehash."""
    g = Gen("A3")
    g.generic_alu = True
    regs = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 19: ("U", "dg"),
            18: ("U", "((0 : BitVec 8)).zeroExtend 32"), 26: ("S", 0x920)}
    params = start(g, regs, {})
    X, Y = "gsVal M0 pk 1 * 2 ^ 256 % p256", "gsVal M0 pk 0x21 * 2 ^ 256 % p256"
    for d, val in ((0x58, X), (0x78, Y), (0x200, "beNat (memBytes M0 rp 32)"), (0xFE4, "beNat (memBytes M0 sq 32)")):
        g.acc[d] = (8, val)
        params.append(f"(a0_{d:x} : accV n0.mem ({gsv.fa(d)}) 8 = {val})")
    params += ["(EC0 : P2vEcCode M0)", "(RS : P2vRoSep B)", "(BY0 : BYEnv M0)",
               "(hrz : beNat (memBytes M0 rp 32) ≠ 0)", "(hsz : beNat (memBytes M0 sq 32) ≠ 0)",
               "(dg_in : P2vIn B dg 32)"]
    ro = "(Or.inr ⟨by decide, by decide⟩)"
    for b0, call, dst, src, n in ((0x186, 0x194, 0xC80, 0x200, 0x20), (0x19C, 0x1B0, 0xCA0, 0xFE4, 0x20),
                                  (0x1B8, 0x1CC, 0x980, 0xC80, 0x40), (0x1D4, 0x1E2, 0xE0, 0x980, 0x40),
                                  (0x1EA, 0x1FA, 0xCA0, 0x78, 0x20), (0x202, 0x210, 0xC80, 0x58, 0x20)):
        g.block(b0, call)
        g.mc(call, dst, src, n)
    g.block(0x218, 0x22E)
    g.mcRo(0x22E, 0xCC0, "BitVec.ofNat 32 (img% p256MontOneAddress)", 0x20, ro, acc=True)
    g.block(0x236, 0x238)
    g.bb(0x238)
    g.block(0x240, 0x25A)
    g.cs2c(0x25A, 0x120, 0xC80, "s1", "(by decide)")
    g.block(0x262, 0x26C)
    g.cs2c(0x26C, 0x140, 0xCA0, "s1", "(by decide)")
    g.block(0x274, 0x27E)
    g.cs2c(0x27E, 0x160, 0xCC0, "s1", "(by decide)")
    g.block(0x286, 0x294)
    g.mc(0x294, 0xC80, 0xE0, 0x20)
    g.block(0x29C, 0x2AC)
    g.nz2(0x2AC, 0x980, 0xC80, "hrz")
    g.block(0x2B4, 0x2C4)
    g.cu2(0x2C4, 0xC80, 0x980)
    g.block(0x2CC, 0x2E2)
    g.mc(0x2E2, 0xFE4, 0x100, 0x20)
    g.block(0x2EA, 0x2FA)
    g.nz2(0x2FA, 0x980, 0xFE4, "hsz")
    g.block(0x302, 0x30C)
    g.cu2(0x30C, 0xCA0, 0x980)
    g.block(0x314, 0x322)
    g.mc(0x322, 0x180, 0xC80, 0x20)
    g.block(0x32A, 0x332)
    g.mc(0x332, 0x1A0, 0xCA0, 0x20)
    g.block(0x33A, 0x33E)
    g.by2(0x33E, 0x1C0, "dg", "dg_in")
    g.block(0x346, 0x348)
    k = g.unz8(0x348, 0x1A0)
    g.set_a0(k, 1, "ite_eq_right hsz")
    g.block(0x350, 0x368)
    g.mcRo(0x368, 0x900, "BitVec.ofNat 32 (img% b2sOrder256Address)", 0x20, ro, acc=True)
    g.store(0x370, "sb")
    g.block(0x374, 0x37C)
    g.mc(0x37C, 0x200, 0x1A0, 0x20)
    g.store(0x384, "sb")
    g.block(0x388, 0x396)
    g.ms0(0x396, 0xFE4, 0x24, accs=(0xFE4,), byts=(0x1004,))
    g.block(0x39E, 0x3B2)
    g.mcRo(0x3B2, 0x980, "BitVec.ofNat 32 (img% p256OneAddress)", 0x20, ro, acc=True)
    g.block(0x3BA, 0x3BC)
    g.store(0x3BC, "sb")
    g.block(0x3C0, 0x3E0)
    stmt, proof = finish(g, 0x3E0, [2, 3, 4, 8, 9, 19, 21, 22, 23, 24, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "p2v_a3", "title": "the P-256 check's inputs",
            "doc": "From 0x186 to the inversion's head at 0x3E0: the key's point at offsets 0x120, 0x140, and "
            "0x160 in projective form, `r` and `s` at 0x180 and 0x1A0, the prehash as a scalar at 0x1C0, and the "
            "order and the inversion's state set up.",
            "params": params, "stmt": stmt, "proof": proof, "binders": EC_BINDERS, "start": 0x186,
            "import": "C3BootProofs.Proofs.P2vMs0"}
    return g, info


IV_ACC = {0x120: "qx", 0x140: "qy", 0x160: "qz", 0x180: "rv", 0x1A0: "sv", 0x1C0: "zv",
          0x200: "gv", 0x900: "fv", 0x980: "ev", 0xFE4: "dv"}
IV_SIGN = {0x220: "gs", 0x920: "fs", 0x9A0: "es", 0x1004: "ds"}
IV_BINDERS = ("{B dlo dhi rem : Word} {fs gs ds es : BitVec 8} {qx qy qz rv sv zv fv gv dv ev : Nat} "
              "{v : Nat → Word} {n0 : Machine}")


def iv_start(g, regs):
    """The inversion of `s`: `f`, `g`, `d`, and `e`, each 8 limbs with a sign
    byte after them, the steps left in `s8`, and `δ` in `s3:s5`, with the
    given registers on top."""
    base = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"),
            19: ("U", "dlo"), 21: ("U", "dhi"), 22: ("C", 1), 23: ("S", 0xCA4), 24: ("U", "rem"), 27: ("C", 7)}
    base.update(regs)
    words = {0x50: ("C", 0x332E3755), 0x54: ("C", 0x11FF43B1)} if 26 not in regs else {}
    params = start(g, base, words)
    for d, nm in sorted(IV_ACC.items()):
        g.acc[d] = (8, nm)
        params.append(f"(a0_{d:x} : accV n0.mem ({gsv.fa(d)}) 8 = {nm})")
    for e, nm in sorted(IV_SIGN.items()):
        g.bytes[e] = nm
        params.append(f"(b0_{e:x} : n0.mem ({gsv.fa(e)}) = {nm})")
    return params


def stage_iva():
    """From the scan's end at 0x3F8 to the divstep loop at 0x43C: the batch's
    size `min rem 62`, the low words of `f` and `g`, and the identity
    matrix."""
    g = Gen("IvA")
    g.generic_alu = True
    params = iv_start(g, {8: ("C", 0x11FF43B1), 9: ("C", 0x332E3755), 26: ("S", 0x920)})
    params += ["(IC0 : P2vIvCode M0)", "(hrem : rem ≠ 0)", "(hfs : fs.toNat ≤ 1)", "(hgs : gs.toNat ≤ 1)"]
    g.store(0x3F8, "sw")
    g.store(0x3FA, "sw")
    g.block(0x3FC, 0x3FE)
    g.umin(0x3FE)
    g.block(0x406, 0x410)
    g.low8(0x410, 0x900, "hfs")
    g.block(0x418, 0x41E)
    g.low8(0x41E, 0x200, "hgs")
    g.block(0x426, 0x438)
    g.branch(0x438, False, f"by rw [g{g.k}_18, s{g.k}.zero]; exact br_beq_f (umin_ne0 hrem)")
    stmt, proof = finish(g, 0x43C, [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
                                    26, 27, 30], set(g.words), set(g.bytes))
    info = {"name": "p2v_iva", "title": "the start of a batch of the inversion of `s`",
            "doc": "From the scan's end at 0x3F8 to the divstep loop at 0x43C: the batch runs `min rem 62` steps, "
            "on the low 64 bits of `f` and `g` as signed words, starting from the identity matrix.",
            "params": params, "stmt": stmt, "proof": proof, "binders": IV_BINDERS, "start": 0x3F8,
            "import": "C3BootProofs.Proofs.P2vIvLib"}
    return g, info


def stage_ivb():
    """From the divstep loop's exit at 0x51E to the batch's end at 0x60C: the
    batch's matrix stored, applied to `f` and `g` and to `d` and `e`, and the
    steps left reduced by the batch's size."""
    g = Gen("IvB")
    g.generic_alu = True
    mat = {9: "ulo", 17: "uhi", 12: "vlo", 16: "vhi", 25: "qlo", 7: "qhi", 30: "rlo", 6: "rhi"}
    regs = {r: ("U", nm) for r, nm in mat.items()}
    regs[18] = ("U", "BitVec.ofNat 32 ns")
    params = iv_start(g, regs)
    params += ["(hns1 : 1 ≤ ns)", "(hns2 : ns ≤ 62)", "(UC0 : P2vUpCode M0)", "(hfs : fs.toNat ≤ 1)",
               "(hgs : gs.toNat ≤ 1)", "(hds : ds.toNat ≤ 1)", "(hes : es.toNat ≤ 1)"]
    g.block(0x51E, 0x526)
    for o in range(0x526, 0x546, 4):
        g.store(o, "sw")
    g.block(0x546, 0x562)
    g.upd8(0x562, "fg", 0xC80, 0x900, 0x200, 0xF80, "ns", "hns1 (by omega)", "hfs", "hgs")
    g.block(0x56A, 0x57E)
    g.mc(0x57E, 0x900, 0xC80, 0x24)
    g.block(0x586, 0x58E)
    g.mc(0x58E, 0x200, 0xCA4, 0x24)
    g.block(0x596, 0x5BE)
    g.load(0x5BE, "lw")
    g.block(0x5C0, 0x5C2)
    g.load(0x5C2, "lw")
    g.block(0x5C4, 0x5C8)
    g.upd8(0x5C8, "de", 0xC80, 0xFE4, 0x980, 0xF80, "ns", "hns1 (by omega)", "hds", "hes",
           extra="(by decide) (by decide) (by decide)", mi_regs=True)
    g.block(0x5D0, 0x5E4)
    g.mc(0x5E4, 0xFE4, 0xC80, 0x24)
    g.block(0x5EC, 0x600)
    g.mc(0x600, 0x980, 0xCA4, 0x24)
    g.block(0x608, 0x60C)
    stmt, proof = finish(g, 0x60C, [2, 3, 4, 8, 9, 19, 21, 22, 23, 24, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "p2v_ivb", "title": "the end of a batch of the inversion of `s`",
            "doc": "From the divstep loop's exit at 0x51E to 0x60C: the batch's matrix is stored at 0xF80, "
            "`update_fg` applies it to `f` and `g` and `update_de` to `d` and `e`, and the steps left drop by "
            "the batch's size.",
            "params": params, "stmt": stmt, "proof": proof,
            "binders": IV_BINDERS.replace("rem : Word}", "rem ulo uhi vlo vhi qlo qhi rlo rhi : Word} {ns : Nat}"),
            "start": 0x51E, "import": "C3BootProofs.Proofs.P2vIvLib"}
    return g, info


def stage_ive():
    """From the inversion's exit at 0x610 to 0x690: `d` normalized by `f`'s
    sign into the inverse of `s`, and `f` checked to be 1."""
    g = Gen("IvE")
    g.generic_alu = True
    g.panics = True
    params = iv_start(g, {8: ("C", 0x11FF43B1), 9: ("C", 0x332E3755), 26: ("S", 0x920)})
    params += ["(UC0 : P2vUpCode M0)", "(EC0 : P2vEcCode M0)",
               "(UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)",
               "(N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code)", "(hfs : fs.toNat ≤ 1)", "(hds : ds.toNat ≤ 1)"]
    g.sign_le = {0x1004: "hds"}
    g.load(0x610, "lbu")
    g.block(0x614, 0x634)
    g.nrm8(0x634, 0xC80, 0xFE4, "(zext_01 hfs)", "BitVec.ofNat 32 (img% b2sOrder256Address)")
    g.block(0x63C, 0x64C)
    k = g.ueq8(0x64C, 0x900, "BitVec.ofNat 32 (img% p256OneAddress)")
    prop = "fv = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8"

    def tail(sub, taken):
        sub.block(0x654, 0x65C)
        sub.bb(0x65C)
        sub.block(0x664, 0x67E)
        sub.mc(0x67E, 0x980, 0xC80, 0x20)
        sub.block(0x686, 0x688)
        sub.store(0x688, "sb")
        sub.branch(0x68C, taken, f"by rw [g{sub.k}_9, g{sub.k}_10]; decide")

    def bad(sub, k=k):
        sub.set_a0(k, 0, "ite_eq_right hf1")
        tail(sub, True)
        sub.fail(sub.fail_proof(("prop", "hf1")), "p2v_panic_10c8")
    g.prop_check(prop, "hf1", bad)
    g.set_a0(k, 1, "ite_eq_left hf1")
    tail(g, False)
    stmt, proof = finish(g, 0x690, [2, 3, 4, 8, 9, 18, 19, 21, 22, 23, 24, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "p2v_ive", "title": "the end of the inversion of `s`",
            "doc": "From the inversion's exit at 0x610 to 0x690: `d`, normalized by `f`'s sign, is the inverse "
            "of `s` at offset 0x980, provided `f` is 1; otherwise `CtOption::unwrap` panics.",
            "params": params, "stmt": stmt, "proof": proof, "binders": IV_BINDERS, "start": 0x610,
            "import": "C3BootProofs.Proofs.P2vIvLib"}
    return g, info


RO = "(Or.inr ⟨by decide, by decide⟩)"
GMONT = "BitVec.ofNat 32 (img% p256GMontAddress)"


def stage_ecd():
    """From 0x690 to the table loop's head at 0x754: `u₁ = z·s⁻¹` and
    `u₂ = r·s⁻¹`, and the two pairs `(G, u₁)` and `(Q, u₂)` laid out for the
    tables."""
    g, params = ecd_gen()
    stmt, proof = finish(g, 0x754, [2, 3, 4, 10, 18, 19, 20, 21, 22, 23, 24, 26, 27], set(g.words), set(g.bytes))
    info = {"name": "p2v_ecd", "title": "`u₁` and `u₂`, and the pairs of the linear combination",
            "doc": "From 0x690 to the table loop at 0x754: `u₁ = z·s⁻¹` and `u₂ = r·s⁻¹` with the scalar field's "
            "`mul`, and the pairs `(G, u₁)` and `(Q, u₂)` copied to offset 0xFE4.",
            "params": params, "stmt": stmt, "proof": proof, "binders": ECD_BINDERS,
            "start": 0x690, "import": "C3BootProofs.Proofs.P2vEcPt"}
    return g, info


ECD_BINDERS = IV_BINDERS.replace("{fs gs ds es : BitVec 8}", "{fs gs ds es : BitVec 8} {wv : Nat}")


def ecd_gen():
    g = Gen("EcD")
    g.generic_alu = True
    params = iv_start(g, {18: ("S", 0xFE4), 26: ("S", 0x920)})
    g.acc[0x980] = (8, "wv")
    params = [p for p in params if not p.startswith("(a0_980 ")]
    params.append("(a0_980 : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x980) 8 = wv)")
    params += ["(RS : P2vRoSep B)", "(PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode)",
               "(WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode)"]
    g.block(0x690, 0x69E)
    g.mc(0x69E, 0x1E0, 0x980, 0x20)
    g.block(0x6A6, 0x6B2)
    g.psm(0x6B2, 0x9E0, 0x1C0, 0x1E0)
    g.block(0x6BA, 0x6C6)
    g.psm(0x6C6, 0xCE0, 0x180, 0x1E0)
    g.block(0x6CE, 0x6E4)
    g.mcRo(0x6E4, 0x980, GMONT, 0x60, RO, acc=8)
    g.block(0x6EC, 0x6FA)
    g.mc(0x6FA, 0xC80, 0x120, 0x60)
    g.block(0x702, 0x710)
    g.mc(0x710, 0x200, 0x980, 0x80)
    g.block(0x718, 0x726)
    g.mc(0x726, 0x280, 0xC80, 0x80)
    g.block(0x72E, 0x73C)
    g.mc(0x73C, 0xFE4, 0x200, 0x100)
    g.block(0x744, 0x754)
    return g, params


def restart(g, name, params):
    h, out = gsv.restart(g, name, params)
    h.__class__ = Gen
    return h, out


ECT_KEEP = {2, 3, 4, 10, 18, 19, 20, 21, 22, 23, 24, 26, 27}
ECT_PARAMS = ["(hP0 : Pt2Lt P0)", "(hP1 : Pt2Lt P1)", "(RS : P2vRoSep B)", "(PT0 : P2vPtCode M0)"]
ECT_BINDERS = ECD_BINDERS.replace("{wv : Nat}", "{wv U1 U2 : Nat} {P0 P1 : Pt2}")


def stage_ect(want):
    """The table loop from 0x754 to 0x862, in six parts `want`: for each
    pair's point `P`, the table `P, 3P, …, 15P`, stored at 0x300 and 0x600."""
    g, params = ecd_gen()
    g.regs = {r: v for r, v in g.regs.items() if r in ECT_KEEP}
    g.ranges = {}
    for d in list(g.acc):
        if 0x200 <= d < 0x300 or 0xFE4 <= d < 0x10E4:
            del g.acc[d]
    g.pt = {0x200: "P0", 0x280: "P1", 0xFE4: "P0", 0x1064: "P1"}
    g.acc.update({0x260: (8, "U1"), 0x2E0: (8, "U2"), 0x1044: (8, "U1"), 0x10C4: (8, "U2")})
    g.pt_lts = {"P0": "hP0", "P1": "hP1"}
    keep = [p for p in params if not p.startswith(gsv.FACT_PARAMS) and not p.startswith(("(PM0 ", "(WM0 "))]
    g, params = restart(g, "EcT0a", keep + ECT_PARAMS)
    parts = {}
    imports = {"0a": "C3BootProofs.Proofs.P2vEcPt", "0c": "C3BootProofs.Proofs.P2vEcT0a",
               "0b": "C3BootProofs.Proofs.P2vEcT0c", "1a": "C3BootProofs.Proofs.P2vEcT0b",
               "1c": "C3BootProofs.Proofs.P2vEcT1a", "1b": "C3BootProofs.Proofs.P2vEcT1c"}

    def cut(g, params, label, off, nxt):
        stmt, proof = finish(g, off, sorted(g.regs), set(g.words), set(g.bytes))
        parts[label] = (g, {"name": f"p2v_ect{label.lower()}", "title": f"the tables of the linear combination, part {label}",
                            "doc": f"Part {label} of the table loop from 0x754 to 0x862: the odd multiples `P + j·2P` of "
                            "`G` and of `Q`, stored at offsets 0x300 and 0x600.",
                            "params": params, "stmt": stmt, "proof": proof, "binders": ECT_BINDERS,
                            "start": g.start_off, "import": imports[label]})
        return restart(g, f"EcT{nxt}", params)
    g.start_off = 0x754
    for i in range(2):
        Pn = f"P{i}"
        g.branch(0x754, False, f"by rw [g{g.k}_19, g{g.k}_20]; decide")
        g.block(0x758, 0x762)
        g.mc(0x762, 0x900, 0xFE4 + 0x80 * i, 0x80)
        g.block(0x76A, 0x774)
        g.branch(0x774, False, f"by rw [g{g.k}_9, s{g.k}.zero]; decide")
        for j in range(8):
            g.block(0x776, 0x77E)
            g.mcRo(0x77E, 0xC80 + 0x60 * j, GMONT, 0x60, RO)
            g.block(0x786, 0x78C)
            g.branch(0x78C, j < 7, f"by rw [g{g.k}_9, s{g.k}.zero]; decide")
        g.block(0x78E, 0x7AE)
        g.mc(0x7AE, 0x980, 0xC80, 0x300)
        g, params = cut(g, params, f"{i}a", 0x7B6, f"{i}c")
        g.start_off = 0x7B6
        g.block(0x7B6, 0x7C6)
        g.pd2(0x7C6, 0xF80, 0x900)
        g.block(0x7CE, 0x7E2)
        g.mc(0x7E2, 0xC80, 0x900, 0x60)
        g.pt[0xC80] = f"tbl2 {Pn} 0"
        g.branch(0x7EA, False, f"by rw [g{g.k}_9, s{g.k}.zero]; decide")
        for j in range(8):
            if j == 4:
                g, params = cut(g, params, f"{i}c", 0x7EC, f"{i}b")
                g.start_off = 0x7EC
            g.block(0x7EC, 0x7FA)
            g.mc(0x7FA, 0x980 + 0x60 * j, 0xC80, 0x60)
            g.block(0x802, 0x812)
            g.pa2(0x812, 0xC80, 0xF80, f"tbl2 {Pn} {j + 1}")
            g.block(0x81A, 0x822)
            g.branch(0x822, j < 7, f"by rw [g{g.k}_9, s{g.k}.zero]; decide")
        g.block(0x824, 0x83C)
        g.mc(0x83C, 0xC80, 0x980, 0x300)
        g.block(0x844, 0x856)
        g.mc(0x856, 0x300 + 0x300 * i, 0xC80, 0x300)
        g.block(0x85E, 0x860)
        g.jump(0x860)
        g.block(0x750, 0x754)
        if i == 0:
            g, params = cut(g, params, "0b", 0x754, "1a")
            g.start_off = 0x754
    g.branch(0x754, True, f"by rw [g{g.k}_19, g{g.k}_20]; decide")
    cut(g, params, "1b", 0x862, "x")
    return parts[want]


EW_BINDERS = "{B : Word} {U1 U2 rv sv zv : Nat} {P0 P1 : Pt2} {v : Nat → Word} {n0 : Machine}"


def stage_ecw(want):
    """From 0x862 to 0x998, in two parts `want`: the width-5 NAF digits of
    `u₁` (part "2", to the loop's second pass at 0x89A) and of `u₂` (part
    "3"), each in a 0x108-byte record with its length, at 0x10E4 and 0x11EC."""
    g, _ = stage_ect("1b")
    g.regs = {r: v for r, v in g.regs.items() if r in (2, 3, 4, 10, 26)}
    g.acc = {d: (8, nm) for d, nm in ((0x180, "rv"), (0x1A0, "sv"), (0x1C0, "zv"), (0x260, "U1"), (0x2E0, "U2"))}
    g.pt = {d: v for d, v in g.pt.items() if 0x300 <= d < 0x900}
    g.words, g.bytes, g.ranges, g.mb = {}, {}, {}, {}
    g.pt_lts = {}
    g, params = restart(g, "EcW", ["(WN0 : P2vWnCode M0)"])
    g.block(0x862, 0x874)
    g.mc(0x874, 0xFE4, 0x200, 0x100)
    g.block(0x87C, 0x896)
    g.branch(0x896, False, f"by rw [g{g.k}_19, s{g.k}.zero]; decide")
    for i in range(2):
        g.block(0x89A, 0x8AA)
        g.mc(0x8AA, 0xF80, 0x1044 + 0x80 * i, 0x20)
        g.block(0x8B2, 0x8C2)
        g.tbb8(0x8C2, 0x980, 0xF80)
        g.block(0x8CA, 0x8D6)
        g.rev(0x8D6, 0x980, 0x20)
        g.block(0x8DE, 0x8F2)
        g.mc(0x8F2, 0x900, 0x980, 0x20)
        g.block(0x8FA, 0x906)
        g.branch(0x906, False, f"by rw [g{g.k}_11, s{g.k}.zero]; decide")
        g.zloop(0x980, 0x101)
        g.block(0x912, 0x924)
        g.mc(0x924, 0xC84, 0x980, 0x101)
        g.block(0x92C, 0x942)
        g.wf(0x942, 0xC84, 0x900)
        g.store(0x94A, "sw")
        g.block(0x94E, 0x962)
        g.mc(0x962, 0x980, 0xC80, 0x108)
        g.block(0x96A, 0x97C)
        g.mc(0x97C, 0x10E4 + 0x108 * i, 0x980, 0x108)
        g.block(0x984, 0x986)
        g.branch(0x986, i == 0, f"by rw [g{g.k}_8, g{g.k}_19]; decide")
        if i == 0:
            stmt, proof = finish(g, 0x89A, sorted(g.regs), set(g.words), set(g.bytes))
            info = {"name": "p2v_ecw2", "title": "the wNAF digits of `u₁`",
                    "doc": "From 0x862 to the loop's second pass at 0x89A: `wnaf_form` writes the width-5 NAF digits "
                    "of `u₁`, which end up in the record at 0x10E4 with their length.",
                    "params": params, "stmt": stmt, "proof": proof, "binders": EW_BINDERS,
                    "start": 0x862, "import": "C3BootProofs.Proofs.P2vEcW"}
            if want == "2":
                return g, info
            g, params = restart(g, "EcW3", params)
    g.load(0x98A, "lw")
    g.block(0x98E, 0x996)
    g.load(0x996, "lw")
    stmt, proof = finish(g, 0x998, sorted(g.regs), set(g.words), set(g.bytes))
    info = {"name": "p2v_ecw3", "title": "the wNAF digits of `u₂`",
            "doc": "From the loop's second pass at 0x89A to 0x998: `wnaf_form` writes the width-5 NAF digits of "
            "`u₂` into the record at 0x11EC, and both lengths are loaded.",
            "params": params, "stmt": stmt, "proof": proof, "binders": EW_BINDERS,
            "start": 0x89A, "import": "C3BootProofs.Proofs.P2vEcW2"}
    return g, info


P256P = "BitVec.ofNat 32 (img% p256ModulusAddress)"
P256R2 = "BitVec.ofNat 32 (img% p256R2Address)"
RO = "(Or.inr ⟨by decide, by decide⟩)"
Z_BINDERS = "{B : Word} {rv X Y Z : Nat} {v : Nat → Word} {n0 : Machine}"


def stage_zs():
    """From 0xB00 to the inversion's head at 0xBEE: the sum copied to 0x1338,
    the field's modulus at 0x980, whether `Z` is nonzero, and the inversion
    of `Z` set up with `f = p`, `g = Z`, `d = 0`, `e = R²`, `δ = 1`, and 591
    steps left."""
    g = Gen("ZS")
    g.generic_alu = True
    params = start(g, {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)")}, {})
    for d, nm in ((0x180, "rv"), (0x980, "X"), (0x9A0, "Y"), (0x9C0, "Z")):
        g.acc[d] = (8, nm)
        params.append(f"(a0_{d:x} : accV n0.mem ({gsv.fa(d)}) 8 = {nm})")
    params += ["(RS : P2vRoSep B)", "(EC0 : P2vEcCode M0)"]
    g.block(0xB00, 0xB14)
    g.mc(0xB14, 0x1338, 0x980, 0x60)
    g.block(0xB1C, 0xB3C)
    g.mcRo(0xB3C, 0x980, P256P, 0x20, RO, acc=True)
    g.block(0xB44, 0xB4E)
    g.store(0xB4E, "sw")
    g.store(0xB52, "sw")
    g.block(0xB56, 0xB68)
    g.mcRo(0xB68, 0x9A0, P256R2, 0x20, RO, acc=True)
    g.block(0xB70, 0xB72)
    k = g.unz8(0xB72, 0x1378)
    nz = "(if Z = 0 then 0 else 1 : Word)"
    g.emit(f"  have g{k}_10 : reg n{k} a0 = {nz} := a0_{k}")
    g.regs[10] = ("U", nz)
    g.block(0xB7A, 0xB7E)
    g.store(0xB7E, "sw")
    g.block(0xB80, 0xB8E)
    g.mcRo(0xB8E, 0xF80, P256P, 0x20, RO, acc=True)
    g.store(0xB96, "sb")
    g.block(0xB9A, 0xBA8)
    g.mc(0xBA8, 0x900, 0x1378, 0x20)
    g.store(0xBB0, "sb")
    g.block(0xBB4, 0xBBC)
    g.ms0(0xBBC, 0x200, 0x24, accs=(0x200,), byts=(0x220,))
    g.block(0xBC4, 0xBD2)
    g.mcRo(0xBD2, 0xFE4, P256R2, 0x20, RO, acc=True)
    g.block(0xBDA, 0xBDE)
    g.store(0xBDE, "sb")
    g.block(0xBE2, 0xBE4)
    g.store(0xBE4, "sw")
    g.block(0xBE6, 0xBEA)
    g.branch(0xBEA, False, f"by rw [g{g.k}_10, s{g.k}.zero]; decide")
    words = {e for e in g.words if e not in (0x9C0, 0x9C4)}
    stmt, proof = finish(g, 0xBEE, [2, 3, 4, 10, 14, 24], words, set(g.bytes))
    info = {"name": "p2v_zs", "title": "the start of the inversion of `Z`",
            "doc": "From 0xB00 to the inversion's head at 0xBEE: the sum moves to 0x1338, the word at 0x10 records "
            "whether its `Z` is nonzero, and the inversion of `Z` starts from `f = p`, `g = Z`, `d = 0`, `e = R²`, "
            "and `δ = 1`, with 591 steps left.",
            "params": params, "stmt": stmt, "proof": proof, "binders": Z_BINDERS, "start": 0xB00,
            "import": "C3BootProofs.Proofs.P2vMs0"}
    return g, info


ZI_ACC = {0x180: "rv", 0x1338: "X", 0x1358: "Y", 0xF80: "fv", 0x900: "gv", 0x200: "dv", 0xFE4: "ev"}
ZI_SIGN = {0xFA0: "fs", 0x920: "gs", 0x220: "ds", 0x1004: "es"}
ZI_BINDERS = ("{B dlo dhi rem nzw : Word} {fs gs ds es : BitVec 8} {" + " ".join(ZI_ACC.values()) + " : Nat} "
              "{v : Nat → Word} {n0 : Machine}")


def zi_start(g, regs, words):
    """The inversion of `Z`: `f`, `g`, `d`, and `e`, each 8 limbs with a sign
    byte after them, the modulus at 0x980, `δ` in 0x40 and `s8`, and `Z`'s
    nonzero flag at 0x10, with the given registers and words on top."""
    base = {2: ("S", 0), 3: ("U", "reg n0 (3 : Fin 32)"), 4: ("U", "reg n0 (4 : Fin 32)"), 24: ("U", "dhi")}
    base.update(regs)
    params = start(g, base, {0x10: "nzw", 0x40: "dlo", **words})
    for d, nm in sorted({**ZI_ACC, 0x980: f"accV M0 ({P256P}) 8"}.items()):
        g.acc[d] = (8, nm)
        params.append(f"(a0_{d:x} : accV n0.mem ({gsv.fa(d)}) 8 = {nm})")
    for e, nm in sorted(ZI_SIGN.items()):
        g.bytes[e] = nm
        params.append(f"(b0_{e:x} : n0.mem ({gsv.fa(e)}) = {nm})")
    return params


def stage_za():
    """From the inversion's head at 0xBEE to the divstep loop at 0xC3C: the
    batch's size `min rem 62`, the low words of `f` and `g`, and the identity
    matrix."""
    g = Gen("ZA")
    g.generic_alu = True
    params = zi_start(g, {10: ("U", "rem"), 14: ("S", 0x920)}, {})
    params += ["(IC0 : P2vIvCode M0)", "(hrem : rem ≠ 0)", "(hfs : fs.toNat ≤ 1)", "(hgs : gs.toNat ≤ 1)"]
    g.store(0xBEE, "sw")
    g.block(0xBF0, 0xBF2)
    g.umin(0xBF2)
    g.block(0xBFA, 0xC04)
    g.low8(0xC04, 0xF80, "hfs")
    g.store(0xC0C, "sw")
    g.store(0xC0E, "sw")
    g.block(0xC10, 0xC18)
    g.low8(0xC18, 0x900, "hgs")
    g.store(0xC20, "sw")
    g.store(0xC22, "sw")
    g.block(0xC24, 0xC26)
    g.store(0xC26, "sw")
    g.block(0xC28, 0xC34)
    g.store(0xC34, "sw")
    g.block(0xC36, 0xC38)
    g.branch(0xC38, False, f"by rw [g{g.k}_9, s{g.k}.zero]; exact br_beq_f (by split; exact hrem; decide)")
    stmt, proof = finish(g, 0xC3C, [2, 3, 4, 8, 9, 13, 14, 18, 20, 22, 23, 24, 25, 26], set(g.words),
                         set(g.bytes))
    info = {"name": "p2v_za", "title": "the start of a batch of the inversion of `Z`",
            "doc": "From the inversion's head at 0xBEE to the divstep loop at 0xC3C: the batch runs `min rem 62` "
            "steps, on the low 64 bits of `f` and `g` as signed words, starting from the identity matrix.",
            "params": params, "stmt": stmt, "proof": proof, "binders": ZI_BINDERS, "start": 0xBEE,
            "import": "C3BootProofs.Proofs.P2vZLib"}
    return g, info


def stage_zb():
    """From the divstep loop's exit at 0xE06 to the batch's branch at 0xEFC:
    the batch's matrix stored, applied to `f` and `g` and to `d` and `e`, and
    the steps left reduced by the batch's size."""
    g = Gen("ZB")
    g.generic_alu = True
    regs = {8: ("S", 0x920), 23: ("U", "ulo"), 26: ("U", "uhi"), 20: ("U", "vlo"), 25: ("U", "vhi"),
            18: ("U", "qhi"), 22: ("U", "rlo"), 13: ("U", "rhi")}
    params = zi_start(g, regs, {0x14: "BitVec.ofNat 32 ns", 0x18: "rem", 0x54: "qlo"})
    params += ["(UC0 : P2vUpCode M0)", "(hns1 : 1 ≤ ns)", "(hns2 : ns ≤ 62)", "(hfs : fs.toNat ≤ 1)",
               "(hgs : gs.toNat ≤ 1)", "(hds : ds.toNat ≤ 1)", "(hes : es.toNat ≤ 1)"]
    g.block(0xE06, 0xE0E)
    for o in (0xE0E, 0xE12, 0xE16, 0xE1A):
        g.store(o, "sw")
    g.load(0xE1E, "lw")
    for o in (0xE20, 0xE24, 0xE28, 0xE2C):
        g.store(o, "sw")
    g.block(0xE30, 0xE50)
    g.load(0xE50, "lw")
    g.block(0xE52, 0xE54)
    g.upd8(0xE54, "fg", 0xC80, 0xF80, 0x900, 0x1318, "ns", "hns1 (by omega)", "hfs", "hgs")
    g.block(0xE5C, 0xE70)
    g.mc(0xE70, 0xF80, 0xC80, 0x24)
    g.block(0xE78, 0xE8C)
    g.mc(0xE8C, 0x900, 0xCA4, 0x24)
    g.block(0xE94, 0xEBC)
    g.upd8(0xEBC, "de", 0xC80, 0x200, 0xFE4, 0x1318, "ns", "hns1 (by omega)", "hds", "hes",
           extra="(by decide) (by decide) (by decide)", cm=0x980)
    g.block(0xEC4, 0xED2)
    g.mc(0xED2, 0x200, 0xC80, 0x24)
    g.block(0xEDA, 0xEEE)
    g.mc(0xEEE, 0xFE4, 0xCA4, 0x24)
    g.block(0xEF6, 0xEF8)
    g.load(0xEF8, "lw")
    g.block(0xEFA, 0xEFC)
    words = {e for e in g.words if e in (0x10, 0x40)}
    stmt, proof = finish(g, 0xEFC, [2, 3, 4, 10, 14, 24], words, set(g.bytes))
    info = {"name": "p2v_zb", "title": "the end of a batch of the inversion of `Z`",
            "doc": "From the divstep loop's exit at 0xE06 to the batch's branch at 0xEFC: the batch's matrix is "
            "stored at 0x1318, `update_fg` applies it to `f` and `g` and `update_de` to `d` and `e` modulo the "
            "field's modulus at 0x980, and the steps left drop by the batch's size.",
            "params": params, "stmt": stmt, "proof": proof,
            "binders": ZI_BINDERS.replace("rem nzw : Word}", "rem nzw ulo uhi vlo vhi qlo qhi rlo rhi : Word} {ns : Nat}"),
            "start": 0xE06, "import": "C3BootProofs.Proofs.P2vZLib"}
    return g, info


RET_PF = "rw [rb{k}]; simp +decide only [runBlock, BInstr.run, svZE10bc, upd, ↓reduceIte]; rw [g{p}_10]; decide"


def stage_ze():
    """From the inversion's exit at 0xF00 to the jump to the epilogue at
    0x10C4: `d` normalized into `Z⁻¹`, kept when `f` is 1 and `Z` is nonzero,
    the affine point `(X·Z⁻¹, Y·Z⁻¹)` or the identity, its `x` as a scalar,
    and the comparison with `r`, which jumps to the epilogue with 0 in `a0`
    when they differ."""
    g = Gen("ZE")
    g.generic_alu = True
    params = zi_start(g, {14: ("S", 0x920)}, {})
    params += ["(UC0 : P2vUpCode M0)", "(EC0 : P2vEcCode M0)",
               "(UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)",
               "(N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code)", "(P2C0 : P2Code M0)",
               "(GDC0 : C3.RV32.Gd.GdCode M0)", "(P2D0 : P2Data M0)",
               "(SC0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode)",
               "(BY0 : BYEnv M0)", "(WN0 : P2vWnCode M0)", "(hfs : fs.toNat ≤ 1)", "(hds : ds.toNat ≤ 1)",
               "(hnz : nzw = 0 ∨ nzw = 1)", "(hX : X < p256)", "(hY : Y < p256)",
               f"(hid : accV M0 ({gsv.ID_AFFINE}) 8 < p256)"]
    g.sign_le = {0x220: "hds"}
    g.load(0xF00, "lbu")
    g.block(0xF04, 0xF18)
    g.nrm8(0xF18, 0x12F4, 0x200, "(zext_01 hfs)", None, cm=0x980)
    zi = g.acc[0x12F4][1]
    params.append(f"(hzi : {zi} < p256)")
    g.block(0xF20, 0xF30)
    k = g.ueq8(0xF30, 0xF80, gsv.ONE256)
    eq = f"(if fv = accV M0 ({gsv.ONE256}) 8 then 1 else 0 : Word)"
    g.emit(f"  have g{k}_10 : reg n{k} a0 = {eq} := a0_{k}")
    g.regs[10] = ("U", eq)
    g.block(0xF38, 0xF3C)
    g.load(0xF3C, "lw")
    g.block(0xF3E, 0xF40)
    g.bb(0xF40)
    g.block(0xF48, 0xF5E)
    g.mc(0xF5E, 0xC80, 0x12F4, 0x20)
    g.store(0xF66, "sb")
    g.block(0xF6A, 0xF78)
    g.ms0(0xF78, 0xFE4, 0x20, accs=(0xFE4,))
    g.block(0xF80, 0xF9C)
    g.csel(0xF9C, 0x980, 0xFE4, 0xC80, "(ch01 hnz)")
    g.store(0xFA4, "sb")
    g.block(0xFA8, 0xFB8)
    g.cmap(0xFB8, 0xFE4, 0x980, "(ch01b hnz)")
    g.block(0xFC0, 0xFCE)
    g.ms0(0xFCE, 0x980, 0x20, accs=(0x980,))
    g.load(0xFD6, "lbu")
    g.block(0xFDA, 0xFEE)
    g.csel(0xFEE, 0x200, 0x980, 0xFE4, "(zext_01b (ch01b hnz))")
    lt0 = "(by repeat' (first | exact hzi | exact p256_pos | apply ite_lt))"
    g.block(0xFF6, 0x1008)
    g.fmul(0x1008, 0xC80, 0x1338, 0x200, "hX", lt0)
    g.block(0x1010, 0x1022)
    g.fmul(0x1022, 0xCA0, 0x1358, 0x200, "hY", lt0)
    g.store(0x102A, "sb")
    g.store(0x102E, "sb")
    g.block(0x1032, 0x104A)
    g.uor(0x104A, 0x980, 0xC80, gsv.ID_AFFINE, "(ch01b hnz)")
    g.block(0x1052, 0x105A)
    g.z32(0x105A, 0x1398)
    g.block(0x1062, 0x1072)
    g.fret(0x1072, 0xC80, 0x980, "(ite_lt (p2fm_lt _ _) hid)")
    g.block(0x107A, 0x108A)
    g.tbb8(0x108A, 0x1398, 0xC80)
    g.block(0x1092, 0x10A2)
    g.by2s(0x10A2, 0xC80, 0x1398)
    g.block(0x10AA, 0x10B4)
    k = g.sct(0x10B4, 0x180, 0xC80)
    prop = f"rv = {g.acc[0xC80][1]}"

    def bad(sub, k=k):
        sub.set_a0(k, 0, "ite_eq_right hxr")
        sub.block(0x10BC, 0x10C4, {10: ("0", RET_PF)})
        sub.jump(0x10C4)
        sub.fail(sub.fail_proof(("prop", "hxr")), "p2v_fail0")
    g.prop_check(prop, "hxr", bad)
    g.set_a0(k, 1, "ite_eq_left hxr")
    g.block(0x10BC, 0x10C4, {10: ("1", RET_PF)})
    stmt, proof = finish(g, 0x10C4, [2, 3, 4, 10], set(), set())
    info = {"name": "p2v_ze", "title": "the end of the check",
            "doc": "From the inversion's exit at 0xF00 to 0x10C4: `d`, normalized by `f`'s sign, is `Z⁻¹` when "
            "`f` is 1 and `Z` is nonzero; the affine `x` of the sum, or the identity's, becomes a scalar, and "
            "the check returns 0 unless it equals `r`.",
            "params": params, "stmt": stmt, "proof": proof, "binders": ZI_BINDERS, "start": 0xF00,
            "import": "C3BootProofs.Proofs.P2vZLib2"}
    return g, info


def stages():
    return {"A1": stage_a1, "A2": stage_a2, "A3": stage_a3, "IvA": stage_iva, "IvB": stage_ivb, "IvE": stage_ive,
            "EcD": stage_ecd, **{f"EcT{w}": (lambda w=w: stage_ect(w)) for w in ("0a", "0c", "0b", "1a", "1c", "1b")},
            "EcW2": lambda: stage_ecw("2"), "EcW3": lambda: stage_ecw("3"), "ZS": stage_zs, "ZA": stage_za,
            "ZB": stage_zb, "ZE": stage_ze}


# Imports that don't reach the `C3.RV32.Sv` namespace.
NO_SV = {"P2vEc", "P2vMs0", "P2vIvLib", "P2vZLib", "P2vZLib2"}

HEADER = """import {imp}

/-!
# `p256VerifyPrehash`: {title}

{doc}
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2{sv}

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
"""


def main():
    stage = sys.argv[1]
    if stage == "--list":
        print("\n".join(stages()))
        return
    g, info = stages()[stage]()
    sv = "" if info["import"].rsplit(".", 1)[1] in NO_SV else " C3.RV32.Sv"
    print(HEADER.format(imp=info["import"], title=info["title"], doc=info["doc"], sv=sv))
    print("\n".join(g.block_defs()))
    print("set_option maxHeartbeats 0 in")
    print(f"theorem {info['name']} " + info["binders"])
    print("    (F : Fr B 0x3590) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)")
    print(f"    (s0 : St n0.mem SV n0 0x{info['start']:X} (reg n0))")
    print("    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)")
    print("    " + "\n    ".join(info["params"]) + " :")
    print(f"    {info['stmt']} := by")
    print("\n".join(g.out))
    print(info["proof"])
    print("")
    print("end C3.RV32.P2v")


if __name__ == "__main__":
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        main()
    sys.stdout.write(gsv.imgnames.add_imports(port(buf.getvalue())))
