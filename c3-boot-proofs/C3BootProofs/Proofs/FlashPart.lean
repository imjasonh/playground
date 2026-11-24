import C3BootProofs.Proofs.FlashRead
import C3BootProofs.Proofs.DerTlv

/-!
# The bootloader's flash `Source`, as compiled

`<FlashPart as Source>::read` reads `out.len()` bytes from `offset` within a
flash partition that starts at `addr` and holds `length` bytes. It checks
that the bytes lie in the partition and that the flash address doesn't
overflow, then tail-calls `flash::read`. The compiled function takes the
partition by value in `a0` and `a1`, the offset in `a2`, and the slice in
`a3` and `a4`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fpr_at_0 : fetchRel flashPartReadCode 0x0 = some (.alu .add a5 a4 a2, 4) := by decide
theorem fpr_at_4 : fetchRel flashPartReadCode 0x4 = some (.branch .bltu a5 a2 0xE, 4) := by decide
theorem fpr_at_8 : fetchRel flashPartReadCode 0x8 = some (.branch .bltu a1 a5 0xA, 4) := by decide
theorem fpr_at_c : fetchRel flashPartReadCode 0xC = some (.alu .add a2 a2 a0, 2) := by decide
theorem fpr_at_e : fetchRel flashPartReadCode 0xE = some (.branch .bgeu a2 a0 0x8, 4) := by decide
theorem fpr_at_12 : fetchRel flashPartReadCode 0x12 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem fpr_at_14 : fetchRel flashPartReadCode 0x14 = some (.jalr x0 ra 0x0, 2) := by decide
theorem fpr_at_16 : fetchRel flashPartReadCode 0x16 = some (.alu .add a0 x0 a2, 2) := by decide
theorem fpr_at_18 : fetchRel flashPartReadCode 0x18 = some (.alu .add a1 x0 a3, 2) := by decide
theorem fpr_at_1a : fetchRel flashPartReadCode 0x1A = some (.alu .add a2 x0 a4, 2) := by decide
theorem fpr_at_1c : fetchRel flashPartReadCode 0x1C = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem fpr_at_20 : fetchRel flashPartReadCode 0x20 = some (.jalr x0 (6 : Fin 32) 0xFFFFFE8C, 4) := by decide
end

theorem fpr_add_toNat {a b : Word} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem fpr_add_wrap {a b : Word} (h : 2 ^ 32 ≤ a.toNat + b.toNat) : (a + b).toNat = a.toNat + b.toNat - 2 ^ 32 := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_add, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show a.toNat + b.toNat - 2 ^ 32 < 2 ^ 32 by omega)]

theorem fpr_ult (a b : Word) : branchTaken .bltu a b = decide (a.toNat < b.toNat) := rfl

theorem fpr_uge (a b : Word) : branchTaken .bgeu a b = !decide (a.toNat < b.toNat) := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `<FlashPart as Source>::read`**, given `RomRead`: called
with a partition at flash address `start` of `plen` bytes, an offset `off`,
and `len` bytes at `out`, it returns 1 or 0 in `a0`. When it returns 1, the
bytes lie in the partition (`off + len ≤ plen`), the flash address
`start + off` doesn't overflow, and the `len` bytes at `out` hold the flash
from `start + off`. It tail-calls `flash::read` at its image address,
`0x158` bytes before its own, which runs on the stack below `sp` that `env`
describes, so it keeps what `flashRead_correct` keeps. -/
theorem flashPartRead_correct {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat}
    (hROM : RomRead flash R romBase romCode) (m : Machine)
    {base G start plen off out len retAddr : Word}
    (hc : CodeIn m.mem base flashPartReadCode) (env : FRdEnv m.mem (base + 0xFFFFFEA8) G out len R romBase romCode)
    (hpc : m.pc = base) (ha0 : reg m a0 = start) (ha1 : reg m a1 = plen) (ha2 : reg m a2 = off)
    (ha3 : reg m a3 = out) (ha4 : reg m a4 = len) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = G + BitVec.ofNat 32 (0x150 + R)) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + BitVec.ofNat 32 (0x150 + R) ∧
      (∀ q, romKeep q = true → reg m' q = reg m q) ∧ (reg m' a0 = 0 ∨ reg m' a0 = 1) ∧
      (reg m' a0 = 1 → off.toNat + len.toNat ≤ plen.toNat ∧ start.toNat + off.toNat < 2 ^ 32 ∧
        ∀ i, i < len.toNat → m'.mem (out + BitVec.ofNat 32 i) = flash (start.toNat + off.toNat + i)) ∧
      ∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the failure exit, from 0x12
  have fail : ∀ {n : Machine} {f : Fin 32 → Word}, St m.mem base n 0x12 f →
      (∀ q, romKeep q = true → f q = reg m q) → f ra = retAddr →
      ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ reg m' sp = G + BitVec.ofNat 32 (0x150 + R) ∧
        (∀ q, romKeep q = true → reg m' q = reg m q) ∧ (reg m' a0 = 0 ∨ reg m' a0 = 1) ∧
        (reg m' a0 = 1 → off.toNat + len.toNat ≤ plen.toNat ∧ start.toNat + off.toNat < 2 ^ 32 ∧
          ∀ i, i < len.toNat → m'.mem (out + BitVec.ofNat 32 i) = flash (start.toNat + off.toNat + i)) ∧
        ∀ x, Sep G (0x150 + R) x 1 → Sep out len.toNat x 1 → m'.mem x = m.mem x := by
    intro n f st kk fra
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc fpr_at_12 (off' := 0x14) (by decide)
    obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.jalr hc fpr_at_14
    have a0v : reg n2 a0 = 0 := by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl
    refine ⟨n2, .cons d1 (.single d2), ?_, ?_, fun q hq => ?_, .inl a0v,
      fun h => absurd (a0v.symm.trans h) (by decide), fun x _ _ => by rw [mem2]⟩
    · rw [pc2, upd_ne' (by decide) st.zero, fra, add_lit_zero, hret]
    · rw [regs2, upd_ne' (by decide) st.zero, kk sp (by decide), hsp]
    · have ha : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
      rw [regs2, upd_ne' ha st.zero]; exact kk q hq
  obtain ⟨n1, d1, u1⟩ := s0.alu hc fpr_at_0 (off' := 0x4) (by decide)
  have k1 : ∀ q, q ≠ a5 → upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2)) q = reg m q :=
    fun q h => upd_ne' h hz
  have v5 : upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2)) a5 = len + off := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ha4, ha2]
  have kr5 : ∀ q, romKeep q = true → upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2)) q = reg m q :=
    fun q hq => k1 q (fun e => by subst e; exact absurd hq (by decide))
  by_cases ov1 : 2 ^ 32 ≤ len.toNat + off.toNat
  · obtain ⟨n2, d2, u2⟩ := u1.taken hc 0x12 fpr_at_4 (by decide) (by
      rw [v5, k1 a2 (by decide), ha2, fpr_ult, fpr_add_wrap ov1]; have := len.isLt; exact decide_eq_true (by omega))
    obtain ⟨m', c', h⟩ := fail u2 kr5 (by rw [k1 ra (by decide), hra])
    exact ⟨m', .cons d1 (.cons d2 c'), h⟩
  have e5 : (len + off).toNat = len.toNat + off.toNat := fpr_add_toNat (by omega)
  obtain ⟨n2, d2, u2⟩ := u1.notTaken hc 0x8 fpr_at_4 (by decide) (by
    rw [v5, k1 a2 (by decide), ha2, fpr_ult, e5]; exact decide_eq_false (by omega))
  by_cases ov2 : plen.toNat < len.toNat + off.toNat
  · obtain ⟨n3, d3, u3⟩ := u2.taken hc 0x12 fpr_at_8 (by decide) (by
      rw [v5, k1 a1 (by decide), ha1, fpr_ult, e5]; exact decide_eq_true ov2)
    obtain ⟨m', c', h⟩ := fail u3 kr5 (by rw [k1 ra (by decide), hra])
    exact ⟨m', .cons d1 (.cons d2 (.cons d3 c')), h⟩
  obtain ⟨n3, d3, u3⟩ := u2.notTaken hc 0xC fpr_at_8 (by decide) (by
    rw [v5, k1 a1 (by decide), ha1, fpr_ult, e5]; exact decide_eq_false ov2)
  obtain ⟨n4, d4, u4⟩ := u3.alu hc fpr_at_c (off' := 0xE) (by decide)
  have v2 : upd (upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2))) a2
      (aluEval .add (upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2)) a2)
        (upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2)) a0)) a2 = off + start := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ha2, ha0]
  have k4 : ∀ q, q ≠ a5 → q ≠ a2 → upd (upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2))) a2
      (aluEval .add (upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2)) a2)
        (upd (reg m) a5 (aluEval .add (reg m a4) (reg m a2)) a0)) q = reg m q :=
    fun q h5 h2 => by rw [upd_ne' h2 (by simp [upd, hz]), k1 q h5]
  by_cases ov3 : 2 ^ 32 ≤ off.toNat + start.toNat
  · obtain ⟨n5, d5, u5⟩ := u4.notTaken hc 0x12 fpr_at_e (by decide) (by
      rw [v2, k4 a0 (by decide) (by decide), ha0, fpr_uge, fpr_add_wrap ov3]; have := off.isLt
      rw [decide_eq_true (show off.toNat + start.toNat - 2 ^ 32 < start.toNat by omega)]; rfl)
    obtain ⟨m', c', h⟩ := fail u5 (fun q hq => k4 q (fun e => by subst e; exact absurd hq (by decide))
      (fun e => by subst e; exact absurd hq (by decide))) (by rw [k4 ra (by decide) (by decide), hra])
    exact ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c')))), h⟩
  have e2 : (off + start).toNat = off.toNat + start.toNat := fpr_add_toNat (by omega)
  obtain ⟨n5, d5, u5⟩ := u4.taken hc 0x16 fpr_at_e (by decide) (by
    rw [v2, k4 a0 (by decide) (by decide), ha0, fpr_uge, e2,
      decide_eq_false (show ¬ off.toNat + start.toNat < start.toNat by omega)]; rfl)
  obtain ⟨n6, c6, u6⟩ := St.block [.alu .add a0 x0 a2, .alu .add a1 x0 a3, .alu .add a2 x0 a4] u5 hc
    (off' := 0x1C) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u6
  obtain ⟨n7, d7, u7⟩ := u6.auipc hc fpr_at_1c (off' := 0x20) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc fpr_at_20
  have hz8 : ∀ (f : Fin 32 → Word), f 0 = 0 → ∀ (r : Fin 32) (v : Word) (q : Fin 32), q ≠ r → upd f r v q = f q :=
    fun f hf r v q h => upd_ne' h hf
  have g8 : ∀ q, reg n8 q = _ := regs8
  have hPe : (base + 0xFFFFFEA8).toNat % 2 = 0 := by
    have := env.hP; rw [this]; decide
  have kq : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a5 → q ≠ t1 → reg n8 q = reg m q := fun q h0 h1 h2 h5 ht => by
    rw [g8]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, hq0, h0, h1, h2, h5, ht, ite_false]
  have pcR : n8.pc = base + 0xFFFFFEA8 := by
    rw [pc8]; simp +decide only [upd_app, ↓reduceIte]
    rw [show base + BitVec.ofNat 32 0x1C + 0x0 + 0xFFFFFE8C = base + 0xFFFFFEA8 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ hPe
  have a0R : reg n8 a0 = off + start := by
    rw [g8]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, zw, ← v2]
    simp +decide only [upd_app, ↓reduceIte]
  have a1R : reg n8 a1 = out := by
    rw [g8]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, zw, ha3]
  have a2R : reg n8 a2 = len := by
    rw [g8]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, zw, ha4]
  have hm8 : n8.mem = m.mem := by rw [mem8]
  obtain ⟨m', c', pc', sp', kk', a0', ok', fr'⟩ := flashRead_correct hROM n8 (P := base + 0xFFFFFEA8)
    (by rw [hm8]; exact env) pcR a0R a1R a2R
    (by rw [kq ra (by decide) (by decide) (by decide) (by decide) (by decide), hra]) hret
    (by rw [kq sp (by decide) (by decide) (by decide) (by decide) (by decide), hsp])
  have hok : start.toNat + off.toNat < 2 ^ 32 := by omega
  refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (.cons d7 (.cons d8 c'))))))), pc', sp',
    fun q hq => ?_, a0', fun h => ⟨by omega, hok, fun i hi => ?_⟩, fun x h1 h2 => by rw [fr' x h1 h2, hm8]⟩
  · rw [kk' q hq]
    exact kq q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
      (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
      (fun e => by subst e; exact absurd hq (by decide))
  · rw [ok' h i hi, e2, Nat.add_comm off.toNat]

end C3.RV32
