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
        """Closes a failing case at 0x142, or with `p2v_fail0` at 0x144 with 0
        in `a0`."""
        k = self.k
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


def stages():
    return {"A1": stage_a1, "A2": stage_a2, "A3": stage_a3}


HEADER = """import {imp}

/-!
# `p256VerifyPrehash`: {title}

{doc}
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

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
    print(HEADER.format(imp=info["import"], title=info["title"], doc=info["doc"]))
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
