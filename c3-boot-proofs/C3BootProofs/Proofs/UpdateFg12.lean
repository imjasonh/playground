import C3BootProofs.Proofs.LincombShift12
import C3BootProofs.Proofs.FromI64

/-!
# `safegcd::update_fg::<12>`

The compiled function turns each row of the transition matrix into two
`Int<2>` values with `Int<2>::from_i64`, and computes the new `f` and `g`
with `lincomb_int_reduce_shift`. `fromI64_correct` and
`lincombShift12_correct` prove the calls.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000

theorem uf12_at_0 : fetchRel updateFg12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem uf12_at_2 : fetchRel updateFg12Code 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem uf12_at_4 : fetchRel updateFg12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem uf12_at_6 : fetchRel updateFg12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem uf12_at_8 : fetchRel updateFg12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem uf12_at_a : fetchRel updateFg12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem uf12_at_c : fetchRel updateFg12Code 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem uf12_at_e : fetchRel updateFg12Code 0xE = some (.alu .add (18 : Fin 32) x0 a4, 2) := by decide
theorem uf12_at_10 : fetchRel updateFg12Code 0x10 = some (.alu .add (9 : Fin 32) x0 a3, 2) := by decide
theorem uf12_at_12 : fetchRel updateFg12Code 0x12 = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem uf12_at_14 : fetchRel updateFg12Code 0x14 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem uf12_at_16 : fetchRel updateFg12Code 0x16 = some (.load .lw a1 a3 0x0, 2) := by decide
theorem uf12_at_18 : fetchRel updateFg12Code 0x18 = some (.load .lw a2 a3 0x4, 2) := by decide
theorem uf12_at_1a : fetchRel updateFg12Code 0x1A = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem uf12_at_1c : fetchRel updateFg12Code 0x1C = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem uf12_at_1e : fetchRel updateFg12Code 0x1E = some (.auipc ra 0x0, 4) := by decide
theorem uf12_at_22 : fetchRel updateFg12Code 0x22 = some (.jalr ra ra 0x11E, 4) := by decide
theorem uf12_at_26 : fetchRel updateFg12Code 0x26 = some (.load .lw a1 (9 : Fin 32) 0x8, 2) := by decide
theorem uf12_at_28 : fetchRel updateFg12Code 0x28 = some (.load .lw a2 (9 : Fin 32) 0xC, 2) := by decide
theorem uf12_at_2a : fetchRel updateFg12Code 0x2A = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem uf12_at_2c : fetchRel updateFg12Code 0x2C = some (.auipc ra 0x0, 4) := by decide
theorem uf12_at_30 : fetchRel updateFg12Code 0x30 = some (.jalr ra ra 0x110, 4) := by decide
theorem uf12_at_34 : fetchRel updateFg12Code 0x34 = some (.aluImm .add a3 sp 0x8, 2) := by decide
theorem uf12_at_36 : fetchRel updateFg12Code 0x36 = some (.aluImm .add a4 sp 0x10, 2) := by decide
theorem uf12_at_38 : fetchRel updateFg12Code 0x38 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem uf12_at_3a : fetchRel updateFg12Code 0x3A = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem uf12_at_3c : fetchRel updateFg12Code 0x3C = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem uf12_at_3e : fetchRel updateFg12Code 0x3E = some (.alu .add a5 x0 (18 : Fin 32), 2) := by decide
theorem uf12_at_40 : fetchRel updateFg12Code 0x40 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem uf12_at_44 : fetchRel updateFg12Code 0x44 = some (.jalr ra ra 0x2B2, 4) := by decide
theorem uf12_at_48 : fetchRel updateFg12Code 0x48 = some (.load .lw a1 (9 : Fin 32) 0x10, 2) := by decide
theorem uf12_at_4a : fetchRel updateFg12Code 0x4A = some (.load .lw a2 (9 : Fin 32) 0x14, 2) := by decide
theorem uf12_at_4c : fetchRel updateFg12Code 0x4C = some (.aluImm .add a0 sp 0x18, 2) := by decide
theorem uf12_at_4e : fetchRel updateFg12Code 0x4E = some (.auipc ra 0x0, 4) := by decide
theorem uf12_at_52 : fetchRel updateFg12Code 0x52 = some (.jalr ra ra 0xEE, 4) := by decide
theorem uf12_at_56 : fetchRel updateFg12Code 0x56 = some (.load .lw a1 (9 : Fin 32) 0x18, 2) := by decide
theorem uf12_at_58 : fetchRel updateFg12Code 0x58 = some (.load .lw a2 (9 : Fin 32) 0x1C, 2) := by decide
theorem uf12_at_5a : fetchRel updateFg12Code 0x5A = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem uf12_at_5c : fetchRel updateFg12Code 0x5C = some (.auipc ra 0x0, 4) := by decide
theorem uf12_at_60 : fetchRel updateFg12Code 0x60 = some (.jalr ra ra 0xE0, 4) := by decide
theorem uf12_at_64 : fetchRel updateFg12Code 0x64 = some (.aluImm .add a0 (8 : Fin 32) 0x34, 4) := by decide
theorem uf12_at_68 : fetchRel updateFg12Code 0x68 = some (.aluImm .add a3 sp 0x18, 2) := by decide
theorem uf12_at_6a : fetchRel updateFg12Code 0x6A = some (.aluImm .add a4 sp 0x20, 2) := by decide
theorem uf12_at_6c : fetchRel updateFg12Code 0x6C = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem uf12_at_6e : fetchRel updateFg12Code 0x6E = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem uf12_at_70 : fetchRel updateFg12Code 0x70 = some (.alu .add a5 x0 (18 : Fin 32), 2) := by decide
theorem uf12_at_72 : fetchRel updateFg12Code 0x72 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem uf12_at_76 : fetchRel updateFg12Code 0x76 = some (.jalr ra ra 0x280, 4) := by decide
theorem uf12_at_7a : fetchRel updateFg12Code 0x7A = some (.load .lw ra sp 0x3C, 2) := by decide
theorem uf12_at_7c : fetchRel updateFg12Code 0x7C = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem uf12_at_7e : fetchRel updateFg12Code 0x7E = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem uf12_at_80 : fetchRel updateFg12Code 0x80 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem uf12_at_82 : fetchRel updateFg12Code 0x82 = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem uf12_at_84 : fetchRel updateFg12Code 0x84 = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem uf12_at_86 : fetchRel updateFg12Code 0x86 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem uf12_at_88 : fetchRel updateFg12Code 0x88 = some (.jalr x0 ra 0x0, 2) := by decide

end

structure UFEnv (M : Word → BitVec 8) (P G out ap bp tp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P updateFg12Code
  fi : CodeIn M (P + 0x13C) fromI64Code
  ls : CodeIn M (P + 0xFFFFF2F2) lincombShift12Code
  lc : CodeIn M (P + 0xFFFFF2F2 + 0x62) lincomb12Code
  abs : CodeIn M (P + 0xFFFFF2F2 + 0x62 + 0xFFFFA54E) absSign2Code
  wide : CodeIn M (P + 0xFFFFF2F2 + 0x62 + 0x398) wideMul12x2Code
  neg : CodeIn M (P + 0xFFFFF2F2 + 0x62 + 0x482) condNeg12Code
  mset : CodeIn M (P + 0xFFFFF2F2 + 0x62 + 0x18A8) memsetCode
  stub : CodeIn M (P + 0xFFFFF2F2 + 0x62 + 0x1910) memcpyStubCode
  body : CodeIn M (P + 0xFFFFF2F2 + 0x62 + 0x1918) memcpyBodyCode
  bsub : CodeIn M (lcBsub (P + 0xFFFFF2F2 + 0x62)) borrowingSubCode
  sel2 : CodeIn M (P + 0xFFFFF2F2 + 0x62 + 0x592) uintSelect2Code
  sel12 : CodeIn M (P + 0xFFFFF2F2 + 0x62 + 0xFFFFFF2A) uintSelect12Code
  zero : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  shr : CodeIn M (P + 0xFFFFF2F2 + 0x1E6) shr12Code
  lm : CodeIn M (P + 0xFFFFF2F2 + 0x1E6 + 0x1EE) leadMut12Code
  tr : CodeIn M (P + 0xFFFFF2F2 + 0x1E6 + 0x1FE) trailing12Code
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x2B0 ≤ 2 ^ 32
  hout : out.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  htp : tp.toNat % 4 = 0
  hwo : out.toNat + 0x65 < 2 ^ 32
  hwa : ap.toNat + 49 < 2 ^ 32
  hwb : bp.toNat + 49 < 2 ^ 32
  sC : Sep G 0x2B0 P updateFg12Code.length
  sF : Sep G 0x2B0 (P + 0x13C) fromI64Code.length
  g_ls : Sep G 0x2B0 (P + 0xFFFFF2F2) lincombShift12Code.length
  g_lc : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62) lincomb12Code.length
  g_abs : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62 + 0xFFFFA54E) absSign2Code.length
  g_wide : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62 + 0x398) wideMul12x2Code.length
  g_neg : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62 + 0x482) condNeg12Code.length
  g_mset : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62 + 0x18A8) memsetCode.length
  g_stub : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62 + 0x1910) memcpyStubCode.length
  g_body : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62 + 0x1918) memcpyBodyCode.length
  g_bsub : Sep G 0x2B0 (lcBsub (P + 0xFFFFF2F2 + 0x62)) borrowingSubCode.length
  g_sel2 : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62 + 0x592) uintSelect2Code.length
  g_sel12 : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x62 + 0xFFFFFF2A) uintSelect12Code.length
  g_zero : Sep G 0x2B0 (BitVec.ofNat 32 u2ZeroAddress) 8
  g_one : Sep G 0x2B0 (BitVec.ofNat 32 u2OneAddress) 8
  g_shr : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x1E6) shr12Code.length
  g_lm : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x1E6 + 0x1EE) leadMut12Code.length
  g_tr : Sep G 0x2B0 (P + 0xFFFFF2F2 + 0x1E6 + 0x1FE) trailing12Code.length
  oC : Sep out 0x65 P updateFg12Code.length
  oF : Sep out 0x65 (P + 0x13C) fromI64Code.length
  o_ls : Sep out 0x65 (P + 0xFFFFF2F2) lincombShift12Code.length
  o_lc : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62) lincomb12Code.length
  o_abs : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62 + 0xFFFFA54E) absSign2Code.length
  o_wide : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62 + 0x398) wideMul12x2Code.length
  o_neg : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62 + 0x482) condNeg12Code.length
  o_mset : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62 + 0x18A8) memsetCode.length
  o_stub : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62 + 0x1910) memcpyStubCode.length
  o_body : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62 + 0x1918) memcpyBodyCode.length
  o_bsub : Sep out 0x65 (lcBsub (P + 0xFFFFF2F2 + 0x62)) borrowingSubCode.length
  o_sel2 : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62 + 0x592) uintSelect2Code.length
  o_sel12 : Sep out 0x65 (P + 0xFFFFF2F2 + 0x62 + 0xFFFFFF2A) uintSelect12Code.length
  o_zero : Sep out 0x65 (BitVec.ofNat 32 u2ZeroAddress) 8
  o_one : Sep out 0x65 (BitVec.ofNat 32 u2OneAddress) 8
  o_shr : Sep out 0x65 (P + 0xFFFFF2F2 + 0x1E6) shr12Code.length
  o_lm : Sep out 0x65 (P + 0xFFFFF2F2 + 0x1E6 + 0x1EE) leadMut12Code.length
  o_tr : Sep out 0x65 (P + 0xFFFFF2F2 + 0x1E6 + 0x1FE) trailing12Code.length
  oG : Sep out 0x65 G 0x2B0
  aG : Sep ap 49 G 0x2B0
  bG : Sep bp 49 G 0x2B0
  tG : Sep tp 32 G 0x2B0
  aO : Sep ap 49 out 0x65
  bO : Sep bp 49 out 0x65
  tO : Sep tp 32 out 0x65

/-- The environment of a `lincomb_int_reduce_shift` call from `update_fg`, with
the result at `res` and the `i64` operands at `cp` and `dp`, in memory that
agrees with the caller's outside its stack and its result. -/
theorem uf12_ls {M M0 : Word → BitVec 8} {P G out ap bp tp res cp dp : Word} (env : UFEnv M0 P G out ap bp tp)
    (hM : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → M x = M0 x)
    (hres : res.toNat % 4 = 0) (hwr : res.toNat + 49 < 2 ^ 32) (rG : Sep res 49 G 0x270)
    (rC : Sep res 49 (P + 0xFFFFF2F2) lincombShift12Code.length)
    (rB : Sep res 49 (P + 0xFFFFF2F2 + 0x62 + 0x1918) memcpyBodyCode.length)
    (hcp : cp.toNat % 4 = 0) (hdp : dp.toNat % 4 = 0) (cG : Sep cp 8 G 0x270) (dG : Sep dp 8 G 0x270) :
    LSEnv M (P + 0xFFFFF2F2) G res ap bp cp dp := by
  have cOf : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep G 0x2B0 b code.length →
      Sep out 0x65 b code.length → CodeIn M b code := fun hc h1 h2 i hi => by
    rw [hM _ (h1.subR (c := i) (l := 1) (by omega)) (h2.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have cOf8 : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep G 0x2B0 b 8 →
      Sep out 0x65 b 8 → code.length = 8 → CodeIn M b code := fun hc h1 h2 hl i hi => by
    rw [hM _ (h1.subR (c := i) (l := 1) (by omega)) (h2.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have g : ∀ {b : Word} {k : Nat}, Sep G 0x2B0 b k → Sep G 0x270 b k := fun h => by
    have := h.sub (c := 0) (l := 0x270) (by decide); rwa [add_ofNat_zero] at this
  exact {
    code := cOf env.ls env.g_ls env.o_ls
    lc := cOf env.lc env.g_lc env.o_lc
    abs := cOf env.abs env.g_abs env.o_abs
    wide := cOf env.wide env.g_wide env.o_wide
    neg := cOf env.neg env.g_neg env.o_neg
    mset := cOf env.mset env.g_mset env.o_mset
    stub := cOf env.stub env.g_stub env.o_stub
    body := cOf env.body env.g_body env.o_body
    bsub := cOf env.bsub env.g_bsub env.o_bsub
    sel2 := cOf env.sel2 env.g_sel2 env.o_sel2
    sel12 := cOf env.sel12 env.g_sel12 env.o_sel12
    zero := cOf8 env.zero env.g_zero env.o_zero (by decide)
    one := cOf8 env.one env.g_one env.o_one (by decide)
    shr := cOf env.shr env.g_shr env.o_shr
    lm := cOf env.lm env.g_lm env.o_lm
    tr := cOf env.tr env.g_tr env.o_tr
    hP := even_at P env.hP 0xFFFFF2F2 (by decide)
    hG := env.hG
    hGt := by have := env.hGt; omega
    hres := hres
    hap := env.hap
    hbp := env.hbp
    hcp := hcp
    hdp := hdp
    hwr := hwr
    hwa := env.hwa
    hwb := env.hwb
    sC := g env.g_ls
    sL := g env.g_lc
    sA := g env.g_abs
    sW := g env.g_wide
    sN := g env.g_neg
    sM := g env.g_mset
    sU := g env.g_stub
    sB := g env.g_body
    sBs := g env.g_bsub
    s2 := g env.g_sel2
    s12 := g env.g_sel12
    sZ := g env.g_zero
    sO := g env.g_one
    sS := g env.g_shr
    sLm := g env.g_lm
    sTr := g env.g_tr
    rG := rG
    aG := (g env.aG.symm).symm
    bG := (g env.bG.symm).symm
    cG := cG
    dG := dG
    rC := rC
    rB := rB }

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev ufPs : List (Fin 32 × Word) :=
  [(ra, 0x3C), ((8 : Fin 32), 0x38), ((9 : Fin 32), 0x34), ((18 : Fin 32), 0x30), ((19 : Fin 32), 0x2C),
   ((20 : Fin 32), 0x28)]

theorem ufPs_range : ∀ p ∈ ufPs, p.2.toNat % 4 = 0 ∧ 0x28 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x40 := by decide

theorem ufPs_sp : ∀ p ∈ ufPs, p.1 ≠ sp := by decide

section
set_option maxRecDepth 20000
theorem ufSave_end : blockEnd updateFg12Code 2 (saveBlock ufPs) = some 0xE := by decide
theorem ufRestore_end : blockEnd updateFg12Code 0x7A (restoreBlock ufPs) = some 0x86 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The prologue, to 0x16: save the registers and keep the arguments in
`s1` through `s4`. -/
theorem uf12_pro (m : Machine) {P F : Word} (hc : CodeIn m.mem P updateFg12Code) (hFa : F.toNat % 4 = 0)
    (sFC : Sep F 0x40 P updateFg12Code.length) (hpc : m.pc = P) (hsp : reg m sp + 0xFFFFFFC0 = F) :
    ∃ n M, Steps m n ∧ St M P n 0x16 (reg n) ∧
      (∀ x, Sep F 0x40 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ ufPs → memLoad32 M (F + o) = reg m r) ∧
      reg n sp = F ∧ reg n (18 : Fin 32) = reg m a4 ∧ reg n (9 : Fin 32) = reg m a3 ∧
      reg n (19 : Fin 32) = reg m a2 ∧ reg n (20 : Fin 32) = reg m a1 ∧
      ∀ q, q.val ∉ [2, 9, 18, 19, 20] → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc uf12_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; exact hsp
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock ufPs) u1 hc ufSave_end (saveBlock_ok _ ufPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (ufPs_range p hp).1, frm_sep' sFC (by have := ufPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0)) ufPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x40 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside ufPs fun p hp => frm_sep' hx (by have := ufPs_range p hp; omega)
  have hcv : CodeIn Msv P updateFg12Code := fun i hi => by
    rw [frSv _ (sFC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have r2 : ∀ q, reg m2 q = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0) q := u2.regs
  have k2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [r2, updz hz h]
  obtain ⟨m3, d3, u3⟩ := u2.self.alu hcv uf12_at_e (off' := 0x10) (by decide)
  have k3 := u3.oldReg u2.self.zero
  obtain ⟨m4, d4, u4⟩ := u3.self.alu hcv uf12_at_10 (off' := 0x12) (by decide)
  have k4 := u4.oldReg u3.self.zero
  obtain ⟨m5, d5, u5⟩ := u4.self.alu hcv uf12_at_12 (off' := 0x14) (by decide)
  have k5 := u5.oldReg u4.self.zero
  obtain ⟨m6, d6, u6⟩ := u5.self.alu hcv uf12_at_14 (off' := 0x16) (by decide)
  have k6 := u6.oldReg u5.self.zero
  have mvv : ∀ (a b : Word), aluEval .add a b = b ∨ a ≠ 0 := fun a b => by
    by_cases h : a = 0
    · left; rw [h]; exact BitVec.zero_add b
    · exact .inr h
  refine ⟨m6, Msv, .cons d1 (c2.trans (.cons d3 (.cons d4 (.cons d5 (.single d6))))), u6.self, frSv,
    fun r o h => ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [← hMsv]
    simp only [ufPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), r2]; exact sp1
  · rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), u3.newReg (by decide)]
    show reg m2 x0 + reg m2 a4 = _; rw [u2.self.zero, k2 _ (by decide)]; exact BitVec.zero_add _
  · rw [k6 _ (by decide), k5 _ (by decide), u4.newReg (by decide)]
    show reg m3 x0 + reg m3 a3 = _; rw [u3.self.zero, k3 _ (by decide), k2 _ (by decide)]; exact BitVec.zero_add _
  · rw [k6 _ (by decide), u5.newReg (by decide)]
    show reg m4 x0 + reg m4 a2 = _
    rw [u4.self.zero, k4 _ (by decide), k3 _ (by decide), k2 _ (by decide)]; exact BitVec.zero_add _
  · rw [u6.newReg (by decide)]
    show reg m5 x0 + reg m5 a1 = _
    rw [u5.self.zero, k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide)]
    exact BitVec.zero_add _
  · have nq : ∀ r : Fin 32, r.val ∈ [2, 9, 18, 19, 20] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k6 q (nq 20 (by decide)), k5 q (nq 19 (by decide)), k4 q (nq 9 (by decide)), k3 q (nq 18 (by decide)),
      k2 q (nq sp (by decide))]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The epilogue, from 0x7A: restore the saved registers and `sp`, and
return. -/
theorem uf12_epi {M : Word → BitVec 8} {P F : Word} {v : Fin 32 → Word} {n : Machine}
    (st : St M P n 0x7A (reg n)) (hc : CodeIn M P updateFg12Code) (hFa : F.toNat % 4 = 0) (rsp : reg n sp = F)
    (hsl : ∀ r o, (r, o) ∈ ufPs → memLoad32 M (F + o) = v r) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧ reg n' sp = F + 0x40 ∧ n'.mem = M ∧
      (∀ r o, (r, o) ∈ ufPs → reg n' r = v r) ∧
      ∀ q, q.val ∉ [1, 8, 9, 18, 19, 20] → q ≠ sp → reg n' q = reg n q := by
  obtain ⟨n4, c4, u4⟩ := St.block (restoreBlock ufPs) st hc ufRestore_end
    (restoreBlock_ok M _ ufPs (reg n) rsp ufPs_sp fun p hp => fr_al' hFa (ufPs_range p hp).1)
  simp only [restoreBlock_run M _ ufPs (reg n) rsp ufPs_sp] at u4
  have rsp4 : restoreRegs M F (reg n) ufPs sp = F := by rw [restoreRegs_sp _ _ _ _ ufPs_sp]; exact rsp
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc uf12_at_86 (off' := 0x88) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc uf12_at_88
  refine ⟨n6, c4.trans (.cons d5 (.single d6)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, hsl ra 0x3C (by decide)]
  · rw [regs6]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp4]; try rfl
  · exact mem6
  · intro r o h
    rw [regs6]
    simp only [ufPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hsl _ _ (by decide)
  · intro q hq hs
    have ne : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19, 20] → q ≠ w := fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n6 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    rw [regs6]
    simp only [upd_app, h0, hs, ite_false]
    simp only [restoreRegs]
    simp only [upd_app, h0, ne ra (by decide), ne 8 (by decide), ne 9 (by decide), ne 18 (by decide),
      ne 19 (by decide), ne 20 (by decide), ite_false]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `from_i64` at `off`: it stores `a1` and `a2` at `d` and
returns to `off + 8`. -/
theorem uf12_fi {M : Word → BitVec 8} {P F d : Word} {n : Machine} {off : Nat} {imm o : Word}
    (st : St M P n off (reg n)) (hc : CodeIn M P updateFg12Code) (hf : CodeIn M (P + 0x13C) fromI64Code)
    (hP : P.toNat % 2 = 0) (h1 : fetchRel updateFg12Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel updateFg12Code (off + 4) = some (.jalr ra ra o, 4)) (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x13C)
    (hoff : (off + 8) % 2 = 0) (hsp : reg n sp = F) (hF : F.toNat % 4 = 0) (hF16 : 16 ≤ F.toNat)
    (ha0 : reg n a0 = d) (hd : d.toNat % 4 = 0)
    (sFC : Sep (F + 0xFFFFFFF0) 16 (P + 0x13C) fromI64Code.length) (sDC : Sep d 8 (P + 0x13C) fromI64Code.length) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 8) (reg n') ∧ reg n' sp = F ∧
      (∀ q, q.val ∉ [1, 11, 12, 13, 14] → reg n' q = reg n q) ∧
      memLoad32 n'.mem d = reg n a1 ∧ memLoad32 n'.mem (d + 4) = reg n a2 ∧
      ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep d 8 x 1 → n'.mem x = M x := by
  obtain ⟨t1, c1, pc1, mem1, regs1⟩ := st.callRa hc h1 h2 hb (even_at P hP 0x13C (by decide))
  have r1 := PEnv.reg1 regs1 st.zero
  obtain ⟨t2, c2, pc2, sp2, k2, lo2, hi2, fr2⟩ := fromI64_correct t1 (by rw [mem1]; exact hf) pc1
    (by rw [r1 _ (by decide), hsp]) (by rw [r1 _ (by decide), ha0]) rfl rfl (by rw [regs1]; simp [upd])
    (even_clear _ (even_at P hP (off + 8) hoff)) hF hF16 hd sFC sDC
  rw [mem1] at fr2
  refine ⟨t2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, ?_, ?_, fr2⟩
  · rw [k2 q (fun h => hq (by revert h; revert q; decide)), r1 q (fun e => hq (by rw [e]; decide))]
  · rw [lo2, r1 _ (by decide)]
  · rw [hi2, r1 _ (by decide)]

/-- The registers `update_fg` keeps across its calls: its frame pointer, the
result, matrix, shift, and operand pointers in `s0` through `s4`, and the
caller's `gp`, `tp`, and `s5` through `s11`. -/
def UFInv (m n : Machine) (F out tp bp ap : Word) (s : Nat) : Prop :=
  reg n sp = F ∧ reg n (8 : Fin 32) = out ∧ reg n (9 : Fin 32) = tp ∧ reg n (18 : Fin 32) = BitVec.ofNat 32 s ∧
    reg n (19 : Fin 32) = bp ∧ reg n (20 : Fin 32) = ap ∧
    ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q

theorem UFInv.tr {m n n' : Machine} {F out tp bp ap : Word} {s : Nat} (h : UFInv m n F out tp bp ap s)
    (k : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) :
    UFInv m n' F out tp bp ap s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(k sp (by decide)).trans h1, (k 8 (by decide)).trans h2, (k 9 (by decide)).trans h3,
    (k 18 (by decide)).trans h4, (k 19 (by decide)).trans h5, (k 20 (by decide)).trans h6,
    fun q hq => (k q (by revert hq; revert q; decide)).trans (h7 q hq)⟩

theorem uf_keep {n n' : Machine} {rd : Fin 32} (k : ∀ q, q ≠ rd → reg n' q = reg n q)
    (h : rd.val ∉ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]) :
    ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q :=
  fun q hq => k q (fun e => h (e ▸ hq))

theorem uf_trans {n n' n'' : Machine}
    (k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q)
    (k2 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n'' q = reg n' q) :
    ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n'' q = reg n q :=
  fun q hq => (k2 q hq).trans (k1 q hq)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Two words of the matrix at `tp + k` into `a1` and `a2`, `a0` at
`F + c`, and a call of `from_i64`: the words land at `F + c`. -/
theorem uf12_seg {M : Word → BitVec 8} {P F tp out bp ap : Word} {m n : Machine} {s off c k : Nat} {imm o : Word}
    (st : St M P n off (reg n)) (hc : CodeIn M P updateFg12Code) (hf : CodeIn M (P + 0x13C) fromI64Code)
    (hP : P.toNat % 2 = 0) (I : UFInv m n F out tp bp ap s)
    (f1 : fetchRel updateFg12Code off = some (.load .lw a1 (9 : Fin 32) (BitVec.ofNat 32 k), 2))
    (f2 : fetchRel updateFg12Code (off + 2) = some (.load .lw a2 (9 : Fin 32) (BitVec.ofNat 32 (k + 4)), 2))
    (f3 : fetchRel updateFg12Code (off + 4) = some (.aluImm .add a0 sp (BitVec.ofNat 32 c), 2))
    (h1 : fetchRel updateFg12Code (off + 6) = some (.auipc ra imm, 4))
    (h2 : fetchRel updateFg12Code (off + 6 + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 (off + 6) + imm + o = P + 0x13C) (hoff : (off + 6 + 8) % 2 = 0)
    (htp : tp.toNat % 4 = 0) (hk : k % 4 = 0) (hF : F.toNat % 4 = 0) (hF16 : 16 ≤ F.toNat) (hcc : c % 4 = 0)
    (sFC : Sep (F + 0xFFFFFFF0) 16 (P + 0x13C) fromI64Code.length)
    (sDC : Sep (F + BitVec.ofNat 32 c) 8 (P + 0x13C) fromI64Code.length) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 6 + 8) (reg n') ∧ UFInv m n' F out tp bp ap s ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 c) = memLoad32 M (tp + BitVec.ofNat 32 k) ∧
      memLoad32 n'.mem (F + BitVec.ofNat 32 c + 4) = memLoad32 M (tp + BitVec.ofNat 32 (k + 4)) ∧
      ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep (F + BitVec.ofNat 32 c) 8 x 1 → n'.mem x = M x := by
  have hsp := I.1
  have h9 := I.2.2.1
  obtain ⟨p1, d1, w1⟩ := st.lwE hc f1 (off' := off + 2) (by rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, ofNat_add_ofNat])
    (by rw [h9]; exact aligned_add htp hk) (v := memLoad32 M (tp + BitVec.ofNat 32 k)) (by rw [h9])
  have k1 := w1.oldReg st.zero
  obtain ⟨p2, d2, w2⟩ := w1.self.lwE hc f2 (off' := off + 4) (by rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, ofNat_add_ofNat])
    (by rw [k1 _ (by decide), h9]; exact aligned_add htp (by omega))
    (v := memLoad32 M (tp + BitVec.ofNat 32 (k + 4))) (by rw [k1 _ (by decide), h9])
  have k2 := w2.oldReg w1.self.zero
  obtain ⟨p3, d3, w3⟩ := w2.self.aluImm hc f3 (off' := off + 6) (by rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, ofNat_add_ofNat])
  have k3 := w3.oldReg w2.self.zero
  have sp3 : reg p3 sp = F := by rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hsp]
  obtain ⟨q, cq, wq, spq, kq, loq, hiq, frq⟩ := uf12_fi w3.self hc hf hP h1 h2 hb hoff sp3 hF hF16
    (by rw [w3.newReg (by decide)]; show reg p2 sp + BitVec.ofNat 32 c = _; rw [k2 _ (by decide), k1 _ (by decide), hsp])
    (aligned_add hF hcc) sFC sDC
  have keep : ∀ q' : Fin 32, q'.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg q q' = reg n q' :=
    fun q' hq => by
      have nq : ∀ r : Fin 32, r.val ∉ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q' ≠ r :=
        fun r hr e => hr (e ▸ hq)
      rw [kq q' (by revert hq; revert q'; decide), k3 q' (nq _ (by decide)), k2 q' (nq _ (by decide)),
        k1 q' (nq _ (by decide))]
  refine ⟨q, .cons d1 (.cons d2 (.cons d3 cq)), wq, ?_, ?_, ?_, frq⟩
  · exact I.tr keep
  · rw [loq, k3 _ (by decide), k2 _ (by decide), w1.newReg (by decide)]
  · rw [hiq, k3 _ (by decide), w2.newReg (by decide)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
/-- **The compiled `safegcd::update_fg::<12>`**, called with the results at
`out`, the signed operands `f` and `g` at `ap` and `bp`, the transition matrix
of four `i64`s at `tp`, and a shift `s` from 1 to 63: the result at `out` is
`lincomb_int_reduce_shift(f, g, t[0][0], t[0][1], s)` and the one at
`out + 0x34` is `lincomb_int_reduce_shift(f, g, t[1][0], t[1][1], s)`, as
`lincombShift12_correct` states them. It returns with `sp` and the
callee-saved registers as they were, and writes nothing outside the 0x2B0
bytes of stack at `G` and the results. -/
theorem updateFg12_correct (m : Machine) {P G out ap bp tp retAddr : Word} {s : Nat}
    (env : UFEnv m.mem P G out ap bp tp) (hpc : m.pc = P) (hsp : reg m sp = G + 0x2B0)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp) (ha3 : reg m a3 = tp)
    (ha4 : reg m a4 = BitVec.ofNat 32 s) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hs1 : 1 ≤ s) (hs2 : s ≤ 63) (hsa : (m.mem (ap + 0x30)).toNat ≤ 1) (hsb : (m.mem (bp + 0x30)).toNat ≤ 1) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x2B0 ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∃ σ A, σ ≤ 1 ∧
        sgnVal σ A = sgnVal (m.mem (ap + 0x30)).toNat (accV m.mem ap 12) * i64Val (accV m.mem tp 2) +
          sgnVal (m.mem (bp + 0x30)).toNat (accV m.mem bp 12) * i64Val (accV m.mem (tp + 8) 2) ∧
        (m'.mem (out + 0x30)).toNat = σ ∧ accV m'.mem out 12 = A / 2 ^ s % 2 ^ 384) ∧
      (∃ σ A, σ ≤ 1 ∧
        sgnVal σ A = sgnVal (m.mem (ap + 0x30)).toNat (accV m.mem ap 12) * i64Val (accV m.mem (tp + 0x10) 2) +
          sgnVal (m.mem (bp + 0x30)).toNat (accV m.mem bp 12) * i64Val (accV m.mem (tp + 0x18) 2) ∧
        (m'.mem (out + 0x34 + 0x30)).toNat = σ ∧ accV m'.mem (out + 0x34) 12 = A / 2 ^ s % 2 ^ 384) ∧
      ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x270 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have tG : ∀ c, c < 0x2B0 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show G.toNat + c < 2 ^ 32 by omega)]
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x270 + c) := fun c => by
    rw [← hF, show (0x270 : Word) = BitVec.ofNat 32 0x270 from rfl, add_ofNat_assoc]
  have eF : F = G + BitVec.ofNat 32 0x270 := hF.symm
  have hFn : F.toNat = G.toNat + 0x270 := by rw [eF, tG _ (by decide)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have aG : ∀ c, c % 4 = 0 → c < 0x2B0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [tG c h2]; have := env.hG; omega
  have sub : ∀ {b : Word} {k : Nat} (c l : Nat), c + l ≤ 0x2B0 → Sep G 0x2B0 b k → Sep (G + BitVec.ofNat 32 c) l b k :=
    fun c l h hs => hs.sub h
  have sG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x2B0 → d + k ≤ 0x2B0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 =>
    sep_offsets G h (by omega) (by omega)
  have g270 : ∀ {b : Word} {k : Nat}, Sep b k G 0x2B0 → Sep b k G 0x270 := fun h => by
    have := h.symm.sub (c := 0) (l := 0x270) (by decide); rw [add_ofNat_zero] at this; exact this.symm
  have inF : ∀ {b : Word} {k : Nat}, Sep G 0x2B0 b k → Sep F 0x40 b k := fun h => by
    rw [eF]; exact sub 0x270 0x40 (by decide) h
  have eS : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x260 := by rw [eF, BitVec.add_assoc]; rfl
  have e8 : F + 8 = G + BitVec.ofNat 32 0x278 := fG 8
  have e10 : F + 0x10 = G + BitVec.ofNat 32 0x280 := fG 0x10
  have e18 : F + 0x18 = G + BitVec.ofNat 32 0x288 := fG 0x18
  have e20 : F + 0x20 = G + BitVec.ofNat 32 0x290 := fG 0x20
  have cOf : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → M x = m.mem x) →
      ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x2B0 b code.length → Sep out 0x65 b code.length →
      CodeIn M b code := fun hM _ _ hc h1 h2 i hi => by
    rw [hM _ (h1.subR (c := i) (l := 1) (by omega)) (h2.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have ldT : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → M x = m.mem x) →
      ∀ c, c + 4 ≤ 32 → memLoad32 M (tp + BitVec.ofNat 32 c) = memLoad32 m.mem (tp + BitVec.ofNat 32 c) :=
    fun hM c hc => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact hM _ (env.tG.symm.subR (c := c + j) (l := 1) (by omega)) (env.tO.symm.subR (c := c + j) (l := 1) (by omega))
  have opG : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → M x = m.mem x) →
      ∀ {b : Word}, Sep b 49 G 0x2B0 → Sep b 49 out 0x65 →
        M (b + 0x30) = m.mem (b + 0x30) ∧ accV M b 12 = accV m.mem b 12 := fun hM _ h1 h2 =>
    ⟨hM _ (h1.symm.subR (c := 0x30) (l := 1) (by omega)) (h2.symm.subR (c := 0x30) (l := 1) (by omega)),
      accV_congr 12 fun i hi => memLoad32_congr fun j hj => hM _ (by
        have := h1.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this) (by
        have := h2.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)⟩
  have tpw : ∀ c, accV m.mem (tp + BitVec.ofNat 32 c) 2 =
      (memLoad32 m.mem (tp + BitVec.ofNat 32 c)).toNat + 2 ^ 32 * (memLoad32 m.mem (tp + BitVec.ofNat 32 (c + 4))).toNat :=
    fun c => by rw [accV_two, show tp + BitVec.ofNat 32 c + 4 = tp + BitVec.ofNat 32 (c + 4) by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
  have hz0 : ∀ {c : Nat}, F + BitVec.ofNat 32 c + 4 = F + BitVec.ofNat 32 (c + 4) := fun {c} => by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  -- the prologue
  obtain ⟨n1, M1, c1, st1, fr1, sl1, sp1, s2_1, s1_1, s3_1, s4_1, k1⟩ :=
    uf12_pro m env.code hFa (inF env.sC) hpc (by rw [hsp, ← hF, BitVec.add_assoc]; rfl)
  have frK1 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → M1 x = m.mem x := fun x hx _ => fr1 x (inF hx)
  have hc1 := cOf frK1 env.code env.sC env.oC
  have hf1 := cOf frK1 env.fi env.sF env.oF
  -- `from_i64(t[0][0])` into `F + 8`
  obtain ⟨p1, dp1, wp1⟩ := st1.lwE hc1 uf12_at_16 (off' := 0x18) (by decide)
    (by rw [k1 _ (by decide), ha3, add_lit_zero]; exact env.htp) (v := memLoad32 m.mem (tp + BitVec.ofNat 32 0))
    (by rw [k1 _ (by decide), ha3, add_lit_zero, ← ldT frK1 0 (by decide), add_ofNat_zero])
  have kp1 := wp1.oldReg st1.zero
  obtain ⟨p2, dp2, wp2⟩ := wp1.self.lwE hc1 uf12_at_18 (off' := 0x1A) (by decide)
    (by rw [kp1 _ (by decide), k1 _ (by decide), ha3]; exact fr_al' env.htp (by decide))
    (v := memLoad32 m.mem (tp + BitVec.ofNat 32 4))
    (by rw [kp1 _ (by decide), k1 _ (by decide), ha3]; exact ldT frK1 4 (by decide))
  have kp2 := wp2.oldReg wp1.self.zero
  obtain ⟨p3, dp3, wp3⟩ := wp2.self.alu hc1 uf12_at_1a (off' := 0x1C) (by decide)
  have kp3 := wp3.oldReg wp2.self.zero
  obtain ⟨p4, dp4, wp4⟩ := wp3.self.aluImm hc1 uf12_at_1c (off' := 0x1E) (by decide)
  have kp4 := wp4.oldReg wp3.self.zero
  have r4 : ∀ q, q ≠ a0 → q ≠ (8 : Fin 32) → q ≠ a1 → q ≠ a2 → reg p4 q = reg n1 q := fun q h0 h8 h1 h2 => by
    rw [kp4 q h0, kp3 q h8, kp2 q h2, kp1 q h1]
  have I4 : UFInv m p4 F out tp bp ap s := by
    refine ⟨by rw [r4 _ (by decide) (by decide) (by decide) (by decide), sp1], ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [kp4 _ (by decide), wp3.newReg (by decide)]; show reg p2 x0 + reg p2 a0 = _
      rw [wp2.self.zero, kp2 _ (by decide), kp1 _ (by decide), k1 _ (by decide), ha0]; exact BitVec.zero_add _
    · rw [r4 _ (by decide) (by decide) (by decide) (by decide), s1_1, ha3]
    · rw [r4 _ (by decide) (by decide) (by decide) (by decide), s2_1, ha4]
    · rw [r4 _ (by decide) (by decide) (by decide) (by decide), s3_1, ha2]
    · rw [r4 _ (by decide) (by decide) (by decide) (by decide), s4_1, ha1]
    · have nq : ∀ r : Fin 32, r.val ∉ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ≠ r := fun r hr e => hr (e ▸ hq)
      rw [r4 q (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)),
        k1 q (by revert hq; revert q; decide)]
  have a0p4 : reg p4 a0 = F + 8 := by
    rw [wp4.newReg (by decide)]; show reg p3 sp + 8 = _
    rw [kp3 _ (by decide), kp2 _ (by decide), kp1 _ (by decide), sp1]
  have a1p4 : reg p4 a1 = memLoad32 m.mem (tp + BitVec.ofNat 32 0) := by
    rw [kp4 _ (by decide), kp3 _ (by decide), kp2 _ (by decide), wp1.newReg (by decide)]
  have a2p4 : reg p4 a2 = memLoad32 m.mem (tp + BitVec.ofNat 32 4) := by
    rw [kp4 _ (by decide), kp3 _ (by decide), wp2.newReg (by decide)]
  obtain ⟨q1, cq1, wq1, spq1, kq1, loq1, hiq1, frq1⟩ := uf12_fi wp4.self hc1 hf1 env.hP uf12_at_1e uf12_at_22
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) I4.1 hFa (by omega) a0p4
    (by rw [e8]; exact aG _ (by decide) (by decide)) (by rw [eS]; exact sub 0x260 16 (by decide) env.sF)
    (by rw [e8]; exact sub 0x278 8 (by decide) env.sF)
  rw [a1p4] at loq1
  rw [a2p4] at hiq1
  have frK2 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → q1.mem x = m.mem x := fun x hx ho => by
    rw [frq1 x (by rw [eS]; exact sub 0x260 16 (by decide) hx) (by rw [e8]; exact sub 0x278 8 (by decide) hx), frK1 x hx ho]
  have I5 := I4.tr fun q hq => kq1 q (by revert hq; revert q; decide)
  have hF16 : 16 ≤ F.toNat := by omega
  have pre : ∀ {x : Word}, Sep G 0x2B0 x 1 → Sep G 0x270 x 1 := fun h => by
    have := h.sub (c := 0) (l := 0x270) (by decide); rwa [add_ofNat_zero] at this
  have scrS : Sep (F + 0xFFFFFFF0) 16 (P + 0x13C) fromI64Code.length := by
    rw [eS]; exact sub 0x260 16 (by decide) env.sF
  have wF : ∀ {M M' : Word → BitVec 8} (c : Nat), c + 4 ≤ 0x40 →
      (∀ j, j < 4 → M' (G + BitVec.ofNat 32 (0x270 + c + j)) = M (G + BitVec.ofNat 32 (0x270 + c + j))) →
      memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) := fun c _ h =>
    memLoad32_congr fun j hj => by rw [fG, add_ofNat_assoc]; exact h j hj
  -- `from_i64(t[0][1])` into `F + 0x10`
  have hc2 := cOf frK2 env.code env.sC env.oC
  have hf2 := cOf frK2 env.fi env.sF env.oF
  obtain ⟨q2, cq2, wq2, I6, lo2, hi2, frq2⟩ := uf12_seg (c := 0x10) (k := 8) wq1 hc2 hf2 env.hP I5
    uf12_at_26 uf12_at_28 uf12_at_2a uf12_at_2c uf12_at_30 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (by decide) env.htp (by decide) hFa hF16 (by decide) scrS (by rw [fG]; exact sub 0x280 8 (by decide) env.sF)
  rw [ldT frK2 8 (by decide)] at lo2
  rw [ldT frK2 12 (by decide)] at hi2
  have frK3 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → q2.mem x = m.mem x := fun x hx ho => by
    rw [frq2 x (by rw [eS]; exact sub 0x260 16 (by decide) hx) (by rw [fG]; exact sub 0x280 8 (by decide) hx),
      frK2 x hx ho]
  have kF2 : ∀ c, c + 4 ≤ 8 → memLoad32 q2.mem (F + BitVec.ofNat 32 (8 + c)) = memLoad32 q1.mem (F + BitVec.ofNat 32 (8 + c)) :=
    fun c hc => wF (8 + c) (by omega) fun j hj => frq2 _ (by rw [eS]; exact sG (.inl (by omega)) (by decide) (by omega))
      (by rw [fG]; exact sG (.inr (by omega)) (by decide) (by omega))
  have cv1 : accV q2.mem (F + 8) 2 = accV m.mem tp 2 := by
    rw [accV_two, accV_two, show F + 8 = F + BitVec.ofNat 32 (8 + 0) from rfl, kF2 0 (by decide),
      show F + BitVec.ofNat 32 (8 + 0) + 4 = F + BitVec.ofNat 32 (8 + 4) from hz0, kF2 4 (by decide),
      show F + BitVec.ofNat 32 (8 + 0) = F + 8 from rfl, loq1, show F + BitVec.ofNat 32 (8 + 4) = F + 8 + 4 from hz0.symm,
      hiq1, add_ofNat_zero]
    rfl
  have cv2 : accV q2.mem (F + 0x10) 2 = accV m.mem (tp + 8) 2 := by
    rw [accV_two, accV_two, show F + 0x10 = F + BitVec.ofNat 32 0x10 from rfl, lo2, hi2,
      show tp + 8 + 4 = tp + BitVec.ofNat 32 (8 + 4) by
        rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
    rfl
  -- `lincomb_int_reduce_shift(f, g, t[0][0], t[0][1], s)` into `out`
  have hc3 := cOf frK3 env.code env.sC env.oC
  have st6 : St q2.mem P q2 0x34 (reg q2) := wq2
  obtain ⟨v1, dv1, wv1⟩ := st6.aluImm hc3 uf12_at_34 (off' := 0x36) (by decide)
  have kv1 := wv1.oldReg st6.zero
  obtain ⟨v2, dv2, wv2⟩ := wv1.self.aluImm hc3 uf12_at_36 (off' := 0x38) (by decide)
  have kv2 := wv2.oldReg wv1.self.zero
  obtain ⟨v3, dv3, wv3⟩ := wv2.self.alu hc3 uf12_at_38 (off' := 0x3A) (by decide)
  have kv3 := wv3.oldReg wv2.self.zero
  obtain ⟨v4, dv4, wv4⟩ := wv3.self.alu hc3 uf12_at_3a (off' := 0x3C) (by decide)
  have kv4 := wv4.oldReg wv3.self.zero
  obtain ⟨v5, dv5, wv5⟩ := wv4.self.alu hc3 uf12_at_3c (off' := 0x3E) (by decide)
  have kv5 := wv5.oldReg wv4.self.zero
  obtain ⟨v6, dv6, wv6⟩ := wv5.self.alu hc3 uf12_at_3e (off' := 0x40) (by decide)
  have kv6 := wv6.oldReg wv5.self.zero
  have Kv : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg v6 q = reg q2 q :=
    uf_trans (uf_trans (uf_trans (uf_trans (uf_trans (uf_keep kv1 (by decide)) (uf_keep kv2 (by decide)))
      (uf_keep kv3 (by decide))) (uf_keep kv4 (by decide))) (uf_keep kv5 (by decide))) (uf_keep kv6 (by decide))
  have I6' := I6.tr Kv
  obtain ⟨t1, ct1, pct1, memt1, regst1⟩ := wv6.self.callRa hc3 uf12_at_40 uf12_at_44 (cb := P + 0xFFFFF2F2)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF2F2 (by decide))
  have rt1 := PEnv.reg1 regst1 wv6.self.zero
  have frT1 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → t1.mem x = m.mem x := fun x hx ho => by
    rw [memt1]; exact frK3 x hx ho
  obtain ⟨n4, σ1, A1, cn4, pcn4, spn4, kn4, sg1, val1, sgo1, mag1, frn4⟩ := lincombShift12_correct t1
    (uf12_ls (res := out) (cp := F + 8) (dp := F + 0x10) env frT1 env.hout (by have := env.hwo; omega) (g270 (sep_pre env.oG (by decide)))
      (sep_pre env.o_ls (by decide)) (sep_pre env.o_body (by decide)) (by rw [e8]; exact aG _ (by decide) (by decide))
      (by rw [e10]; exact aG _ (by decide) (by decide))
      (by rw [e8]; have := sG (c := 0x278) (n := 8) (d := 0) (k := 0x270) (.inr (by decide)) (by decide) (by decide)
          rwa [add_ofNat_zero] at this)
      (by rw [e10]; have := sG (c := 0x280) (n := 8) (d := 0) (k := 0x270) (.inr (by decide)) (by decide) (by decide)
          rwa [add_ofNat_zero] at this))
    pct1 (by rw [rt1 _ (by decide), I6'.1, hF])
    (by rw [rt1 _ (by decide), kv6 _ (by decide), kv5 _ (by decide), kv4 _ (by decide), wv3.newReg (by decide)]
        show reg v2 x0 + reg v2 (8 : Fin 32) = _
        rw [wv2.self.zero, kv2 _ (by decide), kv1 _ (by decide), I6.2.1]; try exact BitVec.zero_add _)
    (by rw [rt1 _ (by decide), kv6 _ (by decide), kv5 _ (by decide), wv4.newReg (by decide)]
        show reg v3 x0 + reg v3 (20 : Fin 32) = _
        rw [wv3.self.zero, kv3 _ (by decide), kv2 _ (by decide), kv1 _ (by decide), I6.2.2.2.2.2.1]
        try exact BitVec.zero_add _)
    (by rw [rt1 _ (by decide), kv6 _ (by decide), wv5.newReg (by decide)]
        show reg v4 x0 + reg v4 (19 : Fin 32) = _
        rw [wv4.self.zero, kv4 _ (by decide), kv3 _ (by decide), kv2 _ (by decide), kv1 _ (by decide),
          I6.2.2.2.2.1]
        try exact BitVec.zero_add _)
    (by rw [rt1 _ (by decide), kv6 _ (by decide), kv5 _ (by decide), kv4 _ (by decide), kv3 _ (by decide),
          kv2 _ (by decide), wv1.newReg (by decide)]
        show reg q2 sp + 8 = _; rw [I6.1])
    (by rw [rt1 _ (by decide), kv6 _ (by decide), kv5 _ (by decide), kv4 _ (by decide), kv3 _ (by decide),
          wv2.newReg (by decide)]
        show reg v1 sp + 0x10 = _; rw [kv1 _ (by decide), I6.1])
    (by rw [rt1 _ (by decide), wv6.newReg (by decide)]
        show reg v5 x0 + reg v5 (18 : Fin 32) = _
        rw [wv5.self.zero, kv5 _ (by decide), kv4 _ (by decide), kv3 _ (by decide), kv2 _ (by decide),
          kv1 _ (by decide), I6.2.2.2.1]
        try exact BitVec.zero_add _)
    (by rw [regst1]; simp [upd]) (even_clear _ (even_at P env.hP (0x40 + 8) (by decide))) hs1 hs2
    (by rw [(opG frT1 env.aG env.aO).1]; exact hsa) (by rw [(opG frT1 env.bG env.bO).1]; exact hsb)
  rw [(opG frT1 env.aG env.aO).1, (opG frT1 env.bG env.bO).1, (opG frT1 env.aG env.aO).2,
    (opG frT1 env.bG env.bO).2, memt1, cv1, cv2] at val1
  have frK4 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → n4.mem x = m.mem x := fun x hx ho => by
    rw [frn4 x (pre hx) (sep_pre ho (by decide)), frT1 x hx ho]
  have I7 : UFInv m n4 F out tp bp ap s := I6'.tr fun q hq => by
    by_cases hs : q = sp
    · subst hs; rw [spn4, I6'.1, hF]
    · rw [kn4 q (by revert hq hs; revert q; decide), rt1 q (fun e => by rw [e] at hq; revert hq; decide)]
  -- `from_i64(t[1][0])` into `F + 0x18` and `from_i64(t[1][1])` into `F + 0x20`
  have st7 : St n4.mem P n4 0x48 (reg n4) := ⟨pcn4, rfl, fun _ => rfl⟩
  obtain ⟨q3, cq3, wq3, I8, lo3, hi3, frq3⟩ := uf12_seg (c := 0x18) (k := 0x10) st7
    (cOf frK4 env.code env.sC env.oC) (cOf frK4 env.fi env.sF env.oF) env.hP I7
    uf12_at_48 uf12_at_4a uf12_at_4c uf12_at_4e uf12_at_52 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (by decide) env.htp (by decide) hFa hF16 (by decide) scrS (by rw [fG]; exact sub 0x288 8 (by decide) env.sF)
  rw [ldT frK4 0x10 (by decide)] at lo3
  rw [ldT frK4 0x14 (by decide)] at hi3
  have frK5 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → q3.mem x = m.mem x := fun x hx ho => by
    rw [frq3 x (by rw [eS]; exact sub 0x260 16 (by decide) hx) (by rw [fG]; exact sub 0x288 8 (by decide) hx),
      frK4 x hx ho]
  obtain ⟨q4, cq4, wq4, I9, lo4, hi4, frq4⟩ := uf12_seg (c := 0x20) (k := 0x18) wq3
    (cOf frK5 env.code env.sC env.oC) (cOf frK5 env.fi env.sF env.oF) env.hP I8
    uf12_at_56 uf12_at_58 uf12_at_5a uf12_at_5c uf12_at_60 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (by decide) env.htp (by decide) hFa hF16 (by decide) scrS (by rw [fG]; exact sub 0x290 8 (by decide) env.sF)
  rw [ldT frK5 0x18 (by decide)] at lo4
  rw [ldT frK5 0x1C (by decide)] at hi4
  have frK6 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → q4.mem x = m.mem x := fun x hx ho => by
    rw [frq4 x (by rw [eS]; exact sub 0x260 16 (by decide) hx) (by rw [fG]; exact sub 0x290 8 (by decide) hx),
      frK5 x hx ho]
  have kF4 : ∀ c, c + 4 ≤ 8 →
      memLoad32 q4.mem (F + BitVec.ofNat 32 (0x18 + c)) = memLoad32 q3.mem (F + BitVec.ofNat 32 (0x18 + c)) :=
    fun c hc => wF (0x18 + c) (by omega) fun j hj => frq4 _ (by rw [eS]; exact sG (.inl (by omega)) (by decide) (by omega))
      (by rw [fG]; exact sG (.inr (by omega)) (by decide) (by omega))
  have tp44 : ∀ c, tp + BitVec.ofNat 32 c + 4 = tp + BitVec.ofNat 32 (c + 4) := fun c => by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  have cv3 : accV q4.mem (F + 0x18) 2 = accV m.mem (tp + 0x10) 2 := by
    rw [accV_two, accV_two, show F + 0x18 = F + BitVec.ofNat 32 (0x18 + 0) from rfl, kF4 0 (by decide),
      show F + BitVec.ofNat 32 (0x18 + 0) + 4 = F + BitVec.ofNat 32 (0x18 + 4) from hz0, kF4 4 (by decide),
      show F + BitVec.ofNat 32 (0x18 + 0) = F + BitVec.ofNat 32 0x18 from rfl, lo3,
      show F + BitVec.ofNat 32 (0x18 + 4) = F + BitVec.ofNat 32 0x18 + 4 from hz0.symm, hi3,
      show tp + 0x10 = tp + BitVec.ofNat 32 0x10 from rfl, tp44]
  have cv4 : accV q4.mem (F + 0x20) 2 = accV m.mem (tp + 0x18) 2 := by
    rw [accV_two, accV_two, show F + 0x20 = F + BitVec.ofNat 32 0x20 from rfl, lo4, hi4,
      show tp + 0x18 = tp + BitVec.ofNat 32 0x18 from rfl, tp44]
  -- `lincomb_int_reduce_shift(f, g, t[1][0], t[1][1], s)` into `out + 0x34`
  have hc6 := cOf frK6 env.code env.sC env.oC
  have st10 : St q4.mem P q4 0x64 (reg q4) := wq4
  obtain ⟨x1, dx1, wx1⟩ := st10.aluImm hc6 uf12_at_64 (off' := 0x68) (by decide)
  have kx1 := wx1.oldReg st10.zero
  obtain ⟨x2, dx2, wx2⟩ := wx1.self.aluImm hc6 uf12_at_68 (off' := 0x6A) (by decide)
  have kx2 := wx2.oldReg wx1.self.zero
  obtain ⟨x3, dx3, wx3⟩ := wx2.self.aluImm hc6 uf12_at_6a (off' := 0x6C) (by decide)
  have kx3 := wx3.oldReg wx2.self.zero
  obtain ⟨x4, dx4, wx4⟩ := wx3.self.alu hc6 uf12_at_6c (off' := 0x6E) (by decide)
  have kx4 := wx4.oldReg wx3.self.zero
  obtain ⟨x5, dx5, wx5⟩ := wx4.self.alu hc6 uf12_at_6e (off' := 0x70) (by decide)
  have kx5 := wx5.oldReg wx4.self.zero
  obtain ⟨x6, dx6, wx6⟩ := wx5.self.alu hc6 uf12_at_70 (off' := 0x72) (by decide)
  have kx6 := wx6.oldReg wx5.self.zero
  have Kx : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg x6 q = reg q4 q :=
    uf_trans (uf_trans (uf_trans (uf_trans (uf_trans (uf_keep kx1 (by decide)) (uf_keep kx2 (by decide)))
      (uf_keep kx3 (by decide))) (uf_keep kx4 (by decide))) (uf_keep kx5 (by decide))) (uf_keep kx6 (by decide))
  have I9' := I9.tr Kx
  obtain ⟨t2, ct2, pct2, memt2, regst2⟩ := wx6.self.callRa hc6 uf12_at_72 uf12_at_76 (cb := P + 0xFFFFF2F2)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF2F2 (by decide))
  have rt2 := PEnv.reg1 regst2 wx6.self.zero
  have frT2 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → t2.mem x = m.mem x := fun x hx ho => by
    rw [memt2]; exact frK6 x hx ho
  have o34 : Sep (out + 0x34) 49 G 0x2B0 := env.oG.sub (c := 0x34) (l := 49) (by decide)
  obtain ⟨n5, σ2, A2, cn5, pcn5, spn5, kn5, sg2, val2, sgo2, mag2, frn5⟩ := lincombShift12_correct t2
    (uf12_ls (res := out + 0x34) (cp := F + 0x18) (dp := F + 0x20) env frT2 (fr_al' env.hout (by decide))
      (by rw [BitVec.toNat_add, show (0x34 : Word).toNat = 0x34 from rfl, Nat.mod_eq_of_lt (by have := env.hwo; omega)]
          have := env.hwo; omega)
      (g270 o34) (env.o_ls.sub (c := 0x34) (l := 49) (by decide)) (env.o_body.sub (c := 0x34) (l := 49) (by decide))
      (by rw [e18]; exact aG _ (by decide) (by decide)) (by rw [e20]; exact aG _ (by decide) (by decide))
      (by rw [e18]; have := sG (c := 0x288) (n := 8) (d := 0) (k := 0x270) (.inr (by decide)) (by decide) (by decide)
          rwa [add_ofNat_zero] at this)
      (by rw [e20]; have := sG (c := 0x290) (n := 8) (d := 0) (k := 0x270) (.inr (by decide)) (by decide) (by decide)
          rwa [add_ofNat_zero] at this))
    pct2 (by rw [rt2 _ (by decide), I9'.1, hF])
    (by rw [rt2 _ (by decide), kx6 _ (by decide), kx5 _ (by decide), kx4 _ (by decide), kx3 _ (by decide),
          kx2 _ (by decide), wx1.newReg (by decide)]
        show reg q4 (8 : Fin 32) + 0x34 = _; rw [I9.2.1])
    (by rw [rt2 _ (by decide), kx6 _ (by decide), kx5 _ (by decide), wx4.newReg (by decide)]
        show reg x3 x0 + reg x3 (20 : Fin 32) = _
        rw [wx3.self.zero, kx3 _ (by decide), kx2 _ (by decide), kx1 _ (by decide), I9.2.2.2.2.2.1]
        try exact BitVec.zero_add _)
    (by rw [rt2 _ (by decide), kx6 _ (by decide), wx5.newReg (by decide)]
        show reg x4 x0 + reg x4 (19 : Fin 32) = _
        rw [wx4.self.zero, kx4 _ (by decide), kx3 _ (by decide), kx2 _ (by decide), kx1 _ (by decide),
          I9.2.2.2.2.1]
        try exact BitVec.zero_add _)
    (by rw [rt2 _ (by decide), kx6 _ (by decide), kx5 _ (by decide), kx4 _ (by decide), kx3 _ (by decide),
          wx2.newReg (by decide)]
        show reg x1 sp + 0x18 = _; rw [kx1 _ (by decide), I9.1])
    (by rw [rt2 _ (by decide), kx6 _ (by decide), kx5 _ (by decide), kx4 _ (by decide), wx3.newReg (by decide)]
        show reg x2 sp + 0x20 = _; rw [kx2 _ (by decide), kx1 _ (by decide), I9.1])
    (by rw [rt2 _ (by decide), wx6.newReg (by decide)]
        show reg x5 x0 + reg x5 (18 : Fin 32) = _
        rw [wx5.self.zero, kx5 _ (by decide), kx4 _ (by decide), kx3 _ (by decide), kx2 _ (by decide),
          kx1 _ (by decide), I9.2.2.2.1]
        try exact BitVec.zero_add _)
    (by rw [regst2]; simp [upd]) (even_clear _ (even_at P env.hP (0x72 + 8) (by decide))) hs1 hs2
    (by rw [(opG frT2 env.aG env.aO).1]; exact hsa) (by rw [(opG frT2 env.bG env.bO).1]; exact hsb)
  rw [(opG frT2 env.aG env.aO).1, (opG frT2 env.bG env.bO).1, (opG frT2 env.aG env.aO).2,
    (opG frT2 env.bG env.bO).2, memt2, cv3, cv4] at val2
  have frK7 : ∀ x, Sep G 0x2B0 x 1 → Sep out 0x65 x 1 → n5.mem x = m.mem x := fun x hx ho => by
    rw [frn5 x (pre hx) (ho.sub (c := 0x34) (l := 49) (by decide)), frT2 x hx ho]
  have I10 : UFInv m n5 F out tp bp ap s := I9'.tr fun q hq => by
    by_cases hs : q = sp
    · subst hs; rw [spn5, I9'.1, hF]
    · rw [kn5 q (by revert hq hs; revert q; decide), rt2 q (fun e => by rw [e] at hq; revert hq; decide)]
  -- the epilogue
  have hc7 := cOf frK7 env.code env.sC env.oC
  have st11 : St n5.mem P n5 0x7A (reg n5) := ⟨pcn5, rfl, fun _ => rfl⟩
  have outF : ∀ c, 0x28 ≤ c → c < 0x40 → ∀ {k : Nat}, k ≤ 0x65 → Sep out k (F + BitVec.ofNat 32 c) 1 :=
    fun c h1 h2 k hk => by rw [fG]; exact (sep_pre env.oG hk).subR (c := 0x270 + c) (l := 1) (by omega)
  have topB : ∀ c, 0x28 ≤ c → c < 0x40 → n5.mem (F + BitVec.ofNat 32 c) = M1 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      have gF : Sep G 0x270 (F + BitVec.ofNat 32 c) 1 := by
        rw [fG]; have := sG (c := 0) (n := 0x270) (d := 0x270 + c) (k := 1) (.inl (by omega)) (by decide) (by omega)
        rwa [add_ofNat_zero] at this
      rw [frn5 _ gF (by rw [fG]; exact o34.subR (c := 0x270 + c) (l := 1) (by omega)), memt2,
        frq4 _ (by rw [eS, fG]; exact sG (.inl (by omega)) (by decide) (by omega))
          (by rw [fG, fG]; exact sG (.inl (by omega)) (by decide) (by omega)),
        frq3 _ (by rw [eS, fG]; exact sG (.inl (by omega)) (by decide) (by omega))
          (by rw [fG, fG]; exact sG (.inl (by omega)) (by decide) (by omega)),
        frn4 _ gF (outF c h1 h2 (by decide)), memt1,
        frq2 _ (by rw [eS, fG]; exact sG (.inl (by omega)) (by decide) (by omega))
          (by rw [fG, fG]; exact sG (.inl (by omega)) (by decide) (by omega)),
        frq1 _ (by rw [eS, fG]; exact sG (.inl (by omega)) (by decide) (by omega))
          (by rw [e8, fG]; exact sG (.inl (by omega)) (by decide) (by omega))]
  have hsl : ∀ r o, (r, o) ∈ ufPs → memLoad32 n5.mem (F + o) = reg m r := fun r o h => by
    have hr : o.toNat % 4 = 0 ∧ 0x28 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x40 := ufPs_range (r, o) h
    rw [← sl1 r o h, ← ofNat_toNat_self o]
    exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact topB _ (by omega) (by omega)
  obtain ⟨n6, cn6, pcn6, spn6, memn6, rsn6, ksn6⟩ := uf12_epi (v := reg m) st11 hc7 hFa I10.1 hsl
  -- the results
  have outB : ∀ c, c < 49 → n5.mem (out + BitVec.ofNat 32 c) = n4.mem (out + BitVec.ofNat 32 c) := fun c hc => by
    have oG' : Sep G 0x2B0 (out + BitVec.ofNat 32 c) 1 := env.oG.symm.subR (c := c) (l := 1) (by omega)
    rw [frn5 _ (pre oG') (sep_offsets out (c := 0x34) (n := 49) (d := c) (k := 1) (.inr (by omega)) (by omega) (by omega)),
      memt2,
      frq4 _ (by rw [eS]; exact (sub 0x260 16 (by decide) env.oG.symm).subR (c := c) (l := 1) (by omega))
        (by rw [fG]; exact (sub 0x290 8 (by decide) env.oG.symm).subR (c := c) (l := 1) (by omega)),
      frq3 _ (by rw [eS]; exact (sub 0x260 16 (by decide) env.oG.symm).subR (c := c) (l := 1) (by omega))
        (by rw [fG]; exact (sub 0x288 8 (by decide) env.oG.symm).subR (c := c) (l := 1) (by omega))]
  refine ⟨n6, c1.trans (.cons dp1 (.cons dp2 (.cons dp3 (.cons dp4 (cq1.trans (cq2.trans (.cons dv1 (.cons dv2
      (.cons dv3 (.cons dv4 (.cons dv5 (.cons dv6 (ct1.trans (cn4.trans (cq3.trans (cq4.trans (.cons dx1 (.cons dx2
      (.cons dx3 (.cons dx4 (.cons dx5 (.cons dx6 (ct2.trans (cn5.trans cn6)))))))))))))))))))))))),
    by rw [pcn6, hra, hret], by rw [spn6, eF, BitVec.add_assoc]; rfl, fun q hq => ?_,
    ⟨σ1, A1, sg1, val1, ?_, ?_⟩, ⟨σ2, A2, sg2, val2, by rw [memn6]; exact sgo2, by rw [memn6]; exact mag2⟩,
    fun x hx ho => by rw [memn6]; exact frK7 x hx ho⟩
  · have hmem : q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
        q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    rcases hmem with rfl | rfl | rfl | rfl | rfl | h
    · exact rsn6 _ 0x38 (by decide)
    · exact rsn6 _ 0x34 (by decide)
    · exact rsn6 _ 0x30 (by decide)
    · exact rsn6 _ 0x2C (by decide)
    · exact rsn6 _ 0x28 (by decide)
    · rw [ksn6 q (by revert h; revert q; decide) (fun e => by rw [e] at h; revert h; decide)]
      exact I10.2.2.2.2.2.2 q h
  · rw [memn6, show out + 0x30 = out + BitVec.ofNat 32 0x30 from rfl, outB _ (by decide)]; exact sgo1
  · rw [memn6, ← mag1]
    exact accV_congr 12 fun i hi => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact outB _ (by omega)

end C3.RV32
