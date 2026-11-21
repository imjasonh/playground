import C3BootProofs.Proofs.SvZLib
import C3BootProofs.Proofs.Pv384HDs4

/-!
# `sigstore::verify`: the constant-time divsteps of the inversion of `Z`

The inversion of the P-256 sum's `Z` runs its divsteps in constant time,
like `p384_verify_prehash`'s (`Pv384HDs.lean`): each step computes both
outcomes and picks one with `select_i64`. Here the whole state lives in
frame slots: `δ` at 0x34, `f` at 0x30 and 0x2C, `g` at 0x24, `u` in `s8` and
at 0x3C, `v` at 0x44 and 0x40, `q` at 0x70 and 0x60, and `r` at 0x5C and
0x74. This file has the loads and stores on the frame, the call to
`select_i64`, and the loop body's blocks between its seven selects.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

theorem zfr_toNat {S a : Word} (hS : S.toNat + 0x1690 ≤ 2 ^ 32) (ha : a.toNat < 0x1690) :
    (S + a).toNat = S.toNat + a.toNat := by
  rw [BitVec.toNat_add]; omega

theorem zfr_sep {S a b : Word} {n k : Nat} (hS : S.toNat + 0x1690 ≤ 2 ^ 32) (hn : 0 < n) (hk : 0 < k)
    (ha : a.toNat + n ≤ 0x1690) (hb : b.toNat + k ≤ 0x1690) (h : a.toNat + n ≤ b.toNat ∨ b.toNat + k ≤ a.toNat) :
    Sep (S + a) n (S + b) k := by
  rcases h with h | h
  · exact sep_of_le (by rw [zfr_toNat hS (by omega), zfr_toNat hS (by omega)]; omega)
      (by rw [zfr_toNat hS (by omega)]; omega)
  · exact (sep_of_le (by rw [zfr_toNat hS (by omega), zfr_toNat hS (by omega)]; omega)
      (by rw [zfr_toNat hS (by omega)]; omega)).symm

/-- A load from one frame slot past a store to another. -/
theorem zld_st {M : Word → BitVec 8} {S a b v : Word} (hS : S.toNat + 0x1690 ≤ 2 ^ 32)
    (ha : a.toNat + 4 ≤ 0x1690) (hb : b.toNat + 4 ≤ 0x1690) (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    memLoad32 (memStore32 M (S + a) v) (S + b) = memLoad32 M (S + b) :=
  memLoad32_store32_sep (zfr_sep hS (by decide) (by decide) ha hb h)

theorem zld_st8 {M : Word → BitVec 8} {S a b : Word} {v : BitVec 8} (hS : S.toNat + 0x1690 ≤ 2 ^ 32)
    (ha : a.toNat + 1 ≤ 0x1690) (hb : b.toNat + 4 ≤ 0x1690) (h : a.toNat + 1 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    memLoad32 (memStore8 M (S + a) v) (S + b) = memLoad32 M (S + b) :=
  memLoad32_store8_sep (zfr_sep hS (by decide) (by decide) ha hb h)

theorem zst8_get {M : Word → BitVec 8} {S a b : Word} {v : BitVec 8} (hS : S.toNat + 0x1690 ≤ 2 ^ 32)
    (ha : a.toNat + 1 ≤ 0x1690) (hb : b.toNat + 1 ≤ 0x1690) (h : a.toNat + 1 ≤ b.toNat ∨ b.toNat + 1 ≤ a.toNat) :
    memStore8 M (S + a) v (S + b) = M (S + b) :=
  memStore8_ne (sep1_ne (zfr_sep hS (by decide) (by decide) ha hb h))

theorem zst32_get {M : Word → BitVec 8} {S a b v : Word} (hS : S.toNat + 0x1690 ≤ 2 ^ 32)
    (ha : a.toNat + 4 ≤ 0x1690) (hb : b.toNat + 1 ≤ 0x1690) (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 1 ≤ a.toNat) :
    memStore32 M (S + a) v (S + b) = M (S + b) :=
  memStore32_get_sep (zfr_sep hS (by decide) (by decide) ha hb h)

/-- A store to the frame keeps a byte at frame offset `e` outside it. -/
theorem zk_st32 {B c v : Word} {M : Word → BitVec 8} {e : Nat} (hS : (B + 0x21A0).toNat + 0x1690 ≤ 2 ^ 32)
    (hc : c.toNat + 4 ≤ 0x1690) (he : e + 1 ≤ 0x1690) (h : c.toNat + 4 ≤ e ∨ e + 1 ≤ c.toNat) :
    memStore32 M (B + 0x21A0 + c) v (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  memStore32_get_sep (zfr_sep hS (by decide) (by decide) hc (by rw [BitVec.toNat_ofNat]; omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h))

theorem zk_st8 {B c : Word} {v : BitVec 8} {M : Word → BitVec 8} {e : Nat}
    (hS : (B + 0x21A0).toNat + 0x1690 ≤ 2 ^ 32)
    (hc : c.toNat + 1 ≤ 0x1690) (he : e + 1 ≤ 0x1690) (h : c.toNat + 1 ≤ e ∨ e + 1 ≤ c.toNat) :
    memStore8 M (B + 0x21A0 + c) v (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  memStore8_ne (sep1_ne (zfr_sep hS (by decide) (by decide) hc (by rw [BitVec.toNat_ofNat]; omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h)))

theorem svR_zst32 {B x c v : Word} {M : Word → BitVec 8} (hx : SvR B x) (hc : c.toNat + 4 ≤ 0x1690) :
    memStore32 M (B + 0x21A0 + c) v x = M x := by
  have := svR_hi (c := c.toNat) (l := 4) hx hc
  rw [ofNat_toNat_self] at this
  exact memStore32_get_sep this

theorem svR_zst8 {B x c : Word} {v : BitVec 8} {M : Word → BitVec 8} (hx : SvR B x) (hc : c.toNat + 1 ≤ 0x1690) :
    memStore8 M (B + 0x21A0 + c) v x = M x := by
  have := svR_hi (c := c.toNat) (l := 1) hx hc
  rw [ofNat_toNat_self] at this
  exact memStore8_ne (sep1_ne this)

theorem zfr_al {B c : Word} (FS : Fr (B + 0x21A0) 0x1690) (hc : c.toNat % 4 = 0) (hc' : c.toNat < 0x1690) :
    (B + 0x21A0 + c).toNat % 4 = 0 := by
  have := FS.al; have := FS.hi; rw [BitVec.toNat_add]; omega

theorem zfr_code {B c : Word} (FS : Fr (B + 0x21A0) 0x1690) {n : Nat} (hc : c.toNat + n ≤ 0x1690) :
    Sep (B + 0x21A0 + c) n SV sigstoreVerifyCode.length := by
  rw [← ofNat_toNat_self c]
  exact FS.sepHi hc (by decide) (by decide)

/-- The block side conditions: aligned stores to the frame, apart from the code. -/
macro "zt_ok" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first
    | exact zfr_al (by assumption) (by decide) (by decide)
    | exact zfr_code (by assumption) (by decide)))

theorem sub_rcomm (a b c : Word) : a - b - c = a - c - b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt; have := c.isLt
  simp only [BitVec.toNat_sub]; omega

theorem ctC1_alt (dl dh : Word) :
    ((0x80000000 - (if (0 : Word).ult dl then 1 else 0) - (dh ^^^ 0x80000000)) &&& (dh ^^^ 0x80000000)) >>> 0x1F =
      ctC1 dl dh := by
  show _ = ((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F
  rw [BitVec.and_comm, sub_rcomm]

set_option maxHeartbeats 4000000 in
/-- A call to `select_i64`, with the choice 0 or 1 in `a0`. -/
theorem sv_si {B : Word} {m : Machine} {off : Nat} {imm o : Word} (F : Fr B 0x3830) (C : SvCode m.mem)
    (IC : SvIvCode m.mem) (s : St m.mem SV m off (reg m))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 selectI64Address)
    (he8 : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x21A0)
    (hc : reg m a0 = 0 ∨ reg m a0 = 1) :
    ∃ m', SvPost B m m' (off + 8) ∧ SvKeepL B m.mem m'.mem [] ∧
      (∀ q : Fin 32, q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg m' q = reg m q) ∧
      reg m' a0 = (if reg m a0 = 1 then reg m a3 else reg m a1) ∧
      reg m' a1 = (if reg m a0 = 1 then reg m a4 else reg m a2) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide)]; exact hsp
  obtain ⟨n2, c2, pc2, sp2, k2, v0, v1, fr2⟩ := selectI64_correct n1 (by rw [mem1]; exact IC.sel64) pc1
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [sp1, sv_sp1]; exact F.sepHi (by decide) (by decide) (by decide))
  have a0e : reg n1 a0 = reg m a0 := r1 a0 (by decide)
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => ?_, fun q hq => ?_⟩, fun e he _ => ?_,
    fun q hr h0 h1' h3 h4 h5 => by rw [k2 q h0 h1' h3 h4 h5, r1 q hr], ?_, ?_⟩
  · rw [fr2 x (fun h => by
      have := svR_sp1 hx 0 (by decide) 0 (by decide)
      rw [add_ofNat_zero, add_ofNat_zero, ← sv_sp1, ← sp1] at this; exact this h.symm), mem1]
  · by_cases h : q = sp
    · subst h; rw [sp2, sp1, hsp]
    · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [fr2 _ (fun h => by
      have := (sepS B (c := 0x219F) (n := 1) (d := 0x21A0 + e) (k := 1) (by omega) (by omega) (by omega)) 0
        (by decide) 0 (by decide)
      rw [add_ofNat_zero, add_ofNat_zero] at this
      rw [sp1, sv_sp1, ← sv_base'] at h; exact this h.symm), mem1]
  · rcases hc with h | h
    · rw [ite_eq_right (by rw [h]; decide), (v0 (by rw [a0e, h]; rfl)).1, r1 a1 (by decide)]
    · rw [ite_eq_left h, (v1 (by rw [a0e, h]; rfl)).1, r1 a3 (by decide)]
  · rcases hc with h | h
    · rw [ite_eq_right (by rw [h]; decide), (v0 (by rw [a0e, h]; rfl)).2, r1 a2 (by decide)]
    · rw [ite_eq_left h, (v1 (by rw [a0e, h]; rfl)).2, r1 a4 (by decide)]

/-- The constant-time loop's state, all in the frame but `u`'s low word in
`s8` (low word first). -/
def ZtRegs (B : Word) (M : Word → BitVec 8) (f : Fin 32 → Word) (s : Ds) : Prop :=
  W64 (memLoad32 M (B + 0x21A0 + 0x34)) (memLoad32 M (B + 0x21A0 + 0x38)) = s.δ ∧
  W64 (memLoad32 M (B + 0x21A0 + 0x30)) (memLoad32 M (B + 0x21A0 + 0x2C)) = s.f ∧
  W64 (memLoad32 M (B + 0x21A0 + 0x24)) (memLoad32 M (B + 0x21A0 + 0x28)) = s.g ∧
  W64 (f 24) (memLoad32 M (B + 0x21A0 + 0x3C)) = s.u ∧
  W64 (memLoad32 M (B + 0x21A0 + 0x44)) (memLoad32 M (B + 0x21A0 + 0x40)) = s.v ∧
  W64 (memLoad32 M (B + 0x21A0 + 0x70)) (memLoad32 M (B + 0x21A0 + 0x60)) = s.q ∧
  W64 (memLoad32 M (B + 0x21A0 + 0x5C)) (memLoad32 M (B + 0x21A0 + 0x74)) = s.r

def zt1 : List BInstr :=
  [.lw (20 : Fin 32) sp 0x24, .aluImm .and (5 : Fin 32) (20 : Fin 32) 0x1, .lui (9 : Fin 32) 0x80000000,
   .lw (6 : Fin 32) sp 0x38, .alu .xor (17 : Fin 32) (6 : Fin 32) (9 : Fin 32), .sb (27 : Fin 32) (5 : Fin 32) 0x0,
   .sw sp (5 : Fin 32) 0x10, .lw a5 sp 0x34, .alu .sltu a2 x0 a5, .aluImm .add a0 sp 0x7FF,
   .aluImm .add a0 a0 0x221, .aluImm .add a1 a5 0x2, .lbu a4 (27 : Fin 32) 0x0, .aluImm .add a6 x0 0x2,
   .alu .sub a3 a6 a5, .alu .sub a2 (9 : Fin 32) a2, .alu .sltu a0 a1 a5, .alu .sub (9 : Fin 32) a2 (17 : Fin 32),
   .alu .add a2 (6 : Fin 32) a0, .alu .and a0 (9 : Fin 32) (17 : Fin 32), .aluImm .srl (8 : Fin 32) a0 0x1F,
   .sw sp (8 : Fin 32) 0xC, .aluImm .sltu a0 a4 0x1, .alu .sub a4 x0 a4, .aluImm .add a0 a0 0xFFFFFFFF,
   .lw (22 : Fin 32) sp 0x30, .alu .and (9 : Fin 32) (22 : Fin 32) a4, .alu .sltu a4 a6 a5,
   .lw (25 : Fin 32) sp 0x2C, .alu .and (21 : Fin 32) (25 : Fin 32) a0, .alu .sub a0 x0 (6 : Fin 32),
   .alu .sub a4 a0 a4, .alu .and (23 : Fin 32) (5 : Fin 32) (8 : Fin 32), .alu .add a0 x0 (23 : Fin 32)]
theorem zt1_end : blockEnd sigstoreVerifyCode 0x1BA4 zt1 = some 0x1C18 := by
  simp only [zt1]
  rw [blockEnd, sv_at_1ba4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ba6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1baa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bb0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bb4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bb8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bbc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bc0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bc4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bc8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bcc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bd0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bd2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bd6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bda]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bde]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1be2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1be6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bf0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bf4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bf8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bfa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1bfc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c00]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c04]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c06]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c0a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c0e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c12]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c16]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def zt2 : List BInstr :=
  [.sw sp a0 0x34, .sw sp a1 0x38, .alu .add a0 x0 (23 : Fin 32), .alu .add a1 x0 (22 : Fin 32),
   .alu .add a2 x0 (25 : Fin 32), .alu .add a3 x0 (20 : Fin 32), .lw (8 : Fin 32) sp 0x28,
   .alu .add a4 x0 (8 : Fin 32)]
theorem zt2_end : blockEnd sigstoreVerifyCode 0x1C20 zt2 = some 0x1C30 := by
  simp only [zt2]
  rw [blockEnd, sv_at_1c20]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c22]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c24]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c26]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c28]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c2a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c2c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c2e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def zt3 : List BInstr :=
  [.sw sp a0 0x30, .sw sp a1 0x2C, .alu .add a1 (9 : Fin 32) (20 : Fin 32), .alu .sltu a2 a1 (9 : Fin 32),
   .alu .add a0 (21 : Fin 32) (8 : Fin 32), .alu .add a2 a2 a0, .alu .sltu a0 (20 : Fin 32) (9 : Fin 32),
   .alu .sub a4 (8 : Fin 32) (21 : Fin 32), .alu .sub a4 a4 a0, .alu .sub a3 (20 : Fin 32) (9 : Fin 32),
   .alu .add a0 x0 (23 : Fin 32)]
theorem zt3_end : blockEnd sigstoreVerifyCode 0x1C38 zt3 = some 0x1C5A := by
  simp only [zt3]
  rw [blockEnd, sv_at_1c38]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c3a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c3c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c40]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c44]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c48]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c4a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c52]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c54]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c58]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def zt4 : List BInstr :=
  [.aluImm .sll a2 a1 0x1F, .aluImm .srl a0 a0 0x1, .alu .or a0 a0 a2, .sw sp a0 0x24, .aluImm .sra a1 a1 0x1,
   .sw sp a1 0x28, .alu .add a0 x0 (23 : Fin 32), .alu .add a1 x0 (24 : Fin 32), .lw (21 : Fin 32) sp 0x3C,
   .alu .add a2 x0 (21 : Fin 32), .lw (9 : Fin 32) sp 0x70, .alu .add a3 x0 (9 : Fin 32), .lw (22 : Fin 32) sp 0x60,
   .alu .add a4 x0 (22 : Fin 32)]
theorem zt4_end : blockEnd sigstoreVerifyCode 0x1C62 zt4 = some 0x1C80 := by
  simp only [zt4]
  rw [blockEnd, sv_at_1c62]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c66]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c68]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c6a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c6c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c6e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c70]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c72]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c74]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c76]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c78]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c7a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c7c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c7e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def zt5 : List BInstr :=
  [.aluImm .srl a2 a0 0x1F, .aluImm .sll a1 a1 0x1, .alu .or a1 a1 a2, .sw sp a1 0x18, .aluImm .sll a0 a0 0x1,
   .sw sp a0 0x14, .alu .add a0 x0 (23 : Fin 32), .lw (8 : Fin 32) sp 0x44, .alu .add a1 x0 (8 : Fin 32),
   .lw (25 : Fin 32) sp 0x40, .alu .add a2 x0 (25 : Fin 32), .lw (20 : Fin 32) sp 0x5C,
   .alu .add a3 x0 (20 : Fin 32), .lw a4 sp 0x74]
theorem zt5_end : blockEnd sigstoreVerifyCode 0x1C88 zt5 = some 0x1CA6 := by
  simp only [zt5]
  rw [blockEnd, sv_at_1c88]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c8c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c8e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c90]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c92]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c94]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c96]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c98]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c9a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c9c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1c9e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ca0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ca2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ca4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def zt6 : List BInstr :=
  [.aluImm .srl a2 a0 0x1F, .aluImm .sll a1 a1 0x1, .aluImm .sll a0 a0 0x1, .sw sp a0 0x4, .alu .or a1 a1 a2,
   .sw sp a1 0x8, .alu .sltu a0 x0 (24 : Fin 32), .alu .sub a4 x0 (21 : Fin 32), .alu .sub a3 x0 (24 : Fin 32),
   .alu .sub a4 a4 a0, .lw (23 : Fin 32) sp 0xC, .alu .add a0 x0 (23 : Fin 32), .alu .add a1 x0 (24 : Fin 32),
   .alu .add a2 x0 (21 : Fin 32)]
theorem zt6_end : blockEnd sigstoreVerifyCode 0x1CAE zt6 = some 0x1CD2 := by
  simp only [zt6]
  rw [blockEnd, sv_at_1cae]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cb2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cb4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cb6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cb8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cba]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cbc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cc0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cc4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cc8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ccc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cd0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def zt7 : List BInstr :=
  [.lw (24 : Fin 32) sp 0x10, .sb (27 : Fin 32) (24 : Fin 32) 0x0, .aluImm .add (21 : Fin 32) sp 0x7FF,
   .aluImm .add (21 : Fin 32) (21 : Fin 32) 0x221, .lbu a2 (27 : Fin 32) 0x0, .alu .sub a3 x0 a2,
   .aluImm .sltu a2 a2 0x1, .alu .and a0 a0 a3, .alu .sltu a4 x0 (8 : Fin 32), .aluImm .add a2 a2 0xFFFFFFFF,
   .alu .and a1 a1 a2, .alu .add (9 : Fin 32) (9 : Fin 32) a0, .sw sp (9 : Fin 32) 0x70,
   .alu .sltu a0 (9 : Fin 32) a0, .alu .add a1 a1 (22 : Fin 32), .alu .sub a2 x0 (25 : Fin 32), .alu .add a0 a0 a1,
   .sw sp a0 0x60, .alu .sub a3 x0 (8 : Fin 32), .alu .sub a4 a2 a4, .alu .add a0 x0 (23 : Fin 32),
   .alu .add a1 x0 (8 : Fin 32), .alu .add a2 x0 (25 : Fin 32)]
theorem zt7_end : blockEnd sigstoreVerifyCode 0x1CDA zt7 = some 0x1D1E := by
  simp only [zt7]
  rw [blockEnd, sv_at_1cda]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cdc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ce0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ce4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1ce8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cf0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cf4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cf6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cfa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cfc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1cfe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d00]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d02]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d06]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d08]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d0c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d0e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d10]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d14]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d18]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d1a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d1c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def zt8 : List BInstr :=
  [.sb (27 : Fin 32) (24 : Fin 32) 0x0, .lbu a2 (27 : Fin 32) 0x0, .lw a3 sp 0x48, .aluImm .add a3 a3 0xFFFFFFFF,
   .sw sp a3 0x48, .lw a3 sp 0x4, .sw sp a3 0x44, .alu .sub a3 x0 a2, .aluImm .sltu a2 a2 0x1,
   .aluImm .add a2 a2 0xFFFFFFFF, .alu .and a0 a0 a3, .alu .and a1 a1 a2, .alu .add (20 : Fin 32) (20 : Fin 32) a0,
   .sw sp (20 : Fin 32) 0x5C, .alu .sltu a0 (20 : Fin 32) a0, .lw a2 sp 0x74, .alu .add a1 a1 a2, .lw a2 sp 0x8,
   .sw sp a2 0x40, .alu .add a0 a0 a1, .sw sp a0 0x74, .lw (24 : Fin 32) sp 0x14, .lw a0 sp 0x18, .sw sp a0 0x3C]
theorem zt8_end : blockEnd sigstoreVerifyCode 0x1D26 zt8 = some 0x1D60 := by
  simp only [zt8]
  rw [blockEnd, sv_at_1d26]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d2a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d2e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d30]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d32]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d34]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d36]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d38]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d3c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d40]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d42]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d44]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d46]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d48]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d4a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d50]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d52]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d54]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d56]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d58]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d5a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d5c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1d5e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

end C3.RV32.Sv
