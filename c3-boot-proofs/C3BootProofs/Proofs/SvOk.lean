import C3BootProofs.Proofs.SvRk

/-!
# `sigstore::verify`: the successful return

After the last validity window, `sigstore::verify` writes `Ok` with the
timestamp's time and the log entry's index to its result and returns.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- Where `sigstore::verify` writes a successful result: 0x18 bytes outside
the stack and the code, at an address that is a multiple of 4. -/
structure SvOutOk (B out : Word) : Prop where
  stk : Sep out 0x18 (B + 0xFFFFEA70) 0x3BF0
  code : Sep out 0x18 SV sigstoreVerifyCode.length
  al : out.toNat % 4 = 0
  fit : out.toNat + 0x18 ≤ 2 ^ 32

/-- `sigstore::verify` returned `Ok`: from `n0`, the machine reaches the
return address with the stack and the callee-saved registers restored, the
discriminant 0 at `out`, the time `(thi, tlo)` at `out + 8`, the index
`(ihi, ilo)` at `out + 0x10`, and memory outside the stack unchanged except
for the 0x18 bytes of the result. -/
def SvOkRet (B out : Word) (v : Nat → Word) (n0 : Machine) (tlo thi ilo ihi : Word) : Prop :=
  ∃ n', Steps n0 n' ∧ n'.pc = v 0 ∧ reg n' sp = B + 0x2660 ∧ (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
    reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧ n'.mem out = 0 ∧
    memLoad32 n'.mem (out + 8) = tlo ∧ memLoad32 n'.mem (out + 0xC) = thi ∧
    memLoad32 n'.mem (out + 0x10) = ilo ∧ memLoad32 n'.mem (out + 0x14) = ihi ∧
    ∀ x, SvR B x → Sep out 0x18 x 1 → n'.mem x = n0.mem x

def svOk : List BInstr :=
  [.sb (18 : Fin 32) x0 0x0, .lw a0 sp 0x3C, .alu .add a1 x0 (18 : Fin 32), .sw a1 a0 0x8, .lw a0 sp 0x7C,
    .sw a1 a0 0xC, .sw (18 : Fin 32) (21 : Fin 32) 0x10, .sw (18 : Fin 32) (24 : Fin 32) 0x14]

theorem svOk_end : blockEnd sigstoreVerifyCode 0x1A9E svOk = some 0x1AB4 := by decide

/-- The memory after the successful result's stores. -/
def svOkMem (M : Word → BitVec 8) (out tlo thi ilo ihi : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore8 M out 0) (out + BitVec.ofNat 32 0x8) tlo)
    (out + BitVec.ofNat 32 0xC) thi) (out + BitVec.ofNat 32 0x10) ilo) (out + BitVec.ofNat 32 0x14) ihi

theorem okSep {out x : Word} {k : Nat} (c : Nat) (hc : c + k ≤ 0x18) (h : Sep out 0x18 x 1) :
    Sep (out + BitVec.ofNat 32 c) k x 1 := h.sub (c := c) (l := k) hc

set_option maxHeartbeats 8000000 in
/-- **The successful exit at 0x1A9E**: store `Ok`, the time, and the index at
`out`, and return. -/
theorem sv_ok_1a9e {B out tlo thi ilo ihi : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660)
    (E : SvCode n.mem) (s : St n.mem SV n 0x1A9E (reg n)) (t : Steps n0 n)
    (fR : ∀ x, SvR B x → n.mem x = n0.mem x) (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (rsp : reg n sp = B + 0x21A0) (hout : reg n (18 : Fin 32) = out) (hO : SvOutOk B out)
    (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32)) (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32))
    (htl : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = tlo)
    (hth : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = thi)
    (h9 : reg n (21 : Fin 32) = ilo) (h7 : reg n (24 : Fin 32) = ihi) :
    SvOkRet B out v n0 tlo thi ilo ihi := by
  have hz := s.zero
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  have sOC := hO.code
  have hof := hO.fit; have hoa := hO.al
  have al : ∀ c : Nat, c % 4 = 0 → c < 0x18 → (out + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c hc hc2 => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have ea : aluEval AluOp.add 0 out = out := by simp only [aluEval]; exact BitVec.zero_add _
  have sc : ∀ c k : Nat, c + k ≤ 0x18 → Sep (out + BitVec.ofNat 32 c) k SV sigstoreVerifyCode.length :=
    fun c k h => sOC.sub (c := c) (l := k) h
  have s0 : Sep out 1 SV sigstoreVerifyCode.length := by
    have := sc 0 1 (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨n1, c1, u1⟩ := s.block svOk E.self svOk_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, svOk]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    have e0 : out + (0x0 : Word) = out := BitVec.add_zero _
    rw [hout, ea, rsp, e0]
    exact ⟨s0, sv_al F (c := 0x3C) (by omega) (by decide), ⟨al 8 (by decide) (by decide), sc 8 4 (by decide)⟩,
      sv_al F (c := 0x7C) (by omega) (by decide), ⟨al 0xC (by decide) (by decide), sc 0xC 4 (by decide)⟩,
      ⟨al 0x10 (by decide) (by decide), sc 0x10 4 (by decide)⟩, al 0x14 (by decide) (by decide), sc 0x14 4 (by decide)⟩)
  have so : ∀ c k d : Nat, c + k ≤ 0x18 → d + 4 ≤ 0x4C0 →
      Sep (out + BitVec.ofNat 32 c) k (B + 0x21A0 + BitVec.ofNat 32 d) 4 := fun c k d h1 h2 => by
    have := (hO.stk.sub (c := c) (l := k) h1).subR (c := 0x1590 + 0x21A0 + d) (l := 4) (by omega)
    rwa [show B + 0xFFFFEA70 + BitVec.ofNat 32 (0x1590 + 0x21A0 + d) = B + 0x21A0 + BitVec.ofNat 32 d by
      rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [show (0xFFFFEA70 : Word).toNat = 0xFFFFEA70 from rfl, show (0x21A0 : Word).toNat = 0x21A0 from rfl]
      omega] at this
  have e0 : out + (0x0 : Word) = out := BitVec.add_zero _
  have z8 : (0 : Word).extractLsb' 0 8 = 0 := rfl
  have L1 : memLoad32 (memStore8 n.mem out 0) (B + 0x21A0 + 60) = tlo := by
    show memLoad32 (memStore8 n.mem out 0) (B + 0x21A0 + BitVec.ofNat 32 0x3C) = tlo
    rw [memLoad32_store8_sep (by have := so 0 1 0x3C (by decide) (by decide); rwa [add_ofNat_zero] at this)]
    exact htl
  have L2 : memLoad32 (memStore32 (memStore8 n.mem out 0) (out + 8) tlo) (B + 0x21A0 + 124) = thi := by
    show memLoad32 (memStore32 (memStore8 n.mem out 0) (out + BitVec.ofNat 32 8) tlo)
      (B + 0x21A0 + BitVec.ofNat 32 0x7C) = thi
    rw [memLoad32_store32_sep (so 8 4 0x7C (by decide) (by decide)),
      memLoad32_store8_sep (by have := so 0 1 0x7C (by decide) (by decide); rwa [add_ofNat_zero] at this)]
    exact hth
  have m1 : (runBlock svOk (n.mem, reg n)).1 = svOkMem n.mem out tlo thi ilo ihi := by
    simp +decide only [runBlock, BInstr.run, svOk, upd, ↓reduceIte]
    rw [hz, hout, e0, ea, rsp, z8, L1, L2, h9, h7]
    rfl
  have r1 : ∀ q, q ≠ a0 → q ≠ a1 → (runBlock svOk (n.mem, reg n)).2 q = reg n q := fun q h0 h1 => by
    simp only [runBlock, BInstr.run, svOk]
    rw [updz (by rfl) h0, updz (by rfl) h1, updz (by rfl) h0]
  have sB : ∀ c k d : Nat, c + k ≤ 0x18 → 0x1590 ≤ d + 0x1590 → d + 4 ≤ 0x2660 →
      Sep (out + BitVec.ofNat 32 c) k (B + BitVec.ofNat 32 d) 4 := fun c k d h1 _ h2 => by
    have := (hO.stk.sub (c := c) (l := k) h1).subR (c := 0x1590 + d) (l := 4) (by omega)
    rwa [show B + 0xFFFFEA70 + BitVec.ofNat 32 (0x1590 + d) = B + BitVec.ofNat 32 d by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [show (0xFFFFEA70 : Word).toNat = 0xFFFFEA70 from rfl]
      omega] at this
  have o0 : out = out + BitVec.ofNat 32 0 := (add_ofNat_zero out).symm
  have s1 : St (svOkMem n.mem out tlo thi ilo ihi) SV n1 0x1AB4 (reg n1) := ⟨u1.pc, u1.mem.trans m1, fun _ => rfl⟩
  have C1 : CodeIn (svOkMem n.mem out tlo thi ilo ihi) SV sigstoreVerifyCode := by
    unfold svOkMem
    exact ((((E.self.store8 s0).store32 (sc 8 4 (by decide))).store32 (sc 0xC 4 (by decide))).store32
      (sc 0x10 4 (by decide))).store32 (sc 0x14 4 (by decide))
  obtain ⟨n2, d2, u2⟩ := s1.jump C1 sv_at_1ab4 (off' := 0x7AE) (by decide) (by rw [s1.pc]; decide)
  have s2 : St (svOkMem n.mem out tlo thi ilo ihi) SV n2 0x7AE (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have hS' : ∀ k, k < 13 → memLoad32 (svOkMem n.mem out tlo thi ilo ihi) (B + BitVec.ofNat 32 (0x265C - 4 * k)) = v k :=
    fun k hk => by
      unfold svOkMem
      rw [memLoad32_store32_sep (sB 0x14 4 _ (by decide) (by omega) (by omega)),
        memLoad32_store32_sep (sB 0x10 4 _ (by decide) (by omega) (by omega)),
        memLoad32_store32_sep (sB 0xC 4 _ (by decide) (by omega) (by omega)),
        memLoad32_store32_sep (sB 8 4 _ (by decide) (by omega) (by omega)),
        memLoad32_store8_sep (by
          have := sB 0 1 (0x265C - 4 * k) (by decide) (by omega) (by omega); rwa [add_ofNat_zero] at this)]
      exact V k hk
  obtain ⟨n3, c3, pc3, mem3, sp3, sv3, g3, t3⟩ := sv_ret (v := v) C1 F s2
    (by rw [u2.regs, u1.regs, r1 sp (by decide) (by decide), rsp]) hS' hret
  have so8 : ∀ c d : Nat, c + 4 ≤ d ∨ d + 4 ≤ c → c + 4 ≤ 0x18 → d + 4 ≤ 0x18 →
      Sep (out + BitVec.ofNat 32 c) 4 (out + BitVec.ofNat 32 d) 4 := fun c d h h1 h2 =>
    sep_offsets out h (by omega) (by omega)
  refine ⟨n3, t.trans (c1.trans ((Steps.single d2).trans c3)), pc3, sp3, sv3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g3, u2.regs, u1.regs, r1 3 (by decide) (by decide), r3]
  · rw [t3, u2.regs, u1.regs, r1 4 (by decide) (by decide), r4]
  · rw [mem3]; unfold svOkMem
    have h1 : ∀ c : Nat, 4 ≤ c → c + 4 ≤ 0x18 → Sep (out + BitVec.ofNat 32 c) 4 out 1 := fun c h1 h2 => by
      have := sep_offsets out (c := c) (n := 4) (d := 0) (k := 1) (Or.inr (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep (h1 0x14 (by decide) (by decide)), memStore32_get_sep (h1 0x10 (by decide) (by decide)),
      memStore32_get_sep (h1 0xC (by decide) (by decide)), memStore32_get_sep (h1 8 (by decide) (by decide)),
      memStore8_same]
  · rw [mem3]; unfold svOkMem
    show memLoad32 _ (out + BitVec.ofNat 32 8) = tlo
    rw [memLoad32_store32_sep (so8 0x14 8 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (so8 0x10 8 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (so8 0xC 8 (by decide) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  · rw [mem3]; unfold svOkMem
    show memLoad32 _ (out + BitVec.ofNat 32 0xC) = thi
    rw [memLoad32_store32_sep (so8 0x14 0xC (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (so8 0x10 0xC (by decide) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  · rw [mem3]; unfold svOkMem
    show memLoad32 _ (out + BitVec.ofNat 32 0x10) = ilo
    rw [memLoad32_store32_sep (so8 0x14 0x10 (by decide) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  · rw [mem3]; unfold svOkMem
    exact memLoad32_store32_same _ _ _
  · intro x hx hs
    rw [mem3]; unfold svOkMem
    rw [memStore32_get_sep (hs.sub (c := 0x14) (l := 4) (by decide) |>.symm |> fun h => h.symm),
      memStore32_get_sep (hs.sub (c := 0x10) (l := 4) (by decide)),
      memStore32_get_sep (hs.sub (c := 0xC) (l := 4) (by decide)),
      memStore32_get_sep (hs.sub (c := 8) (l := 4) (by decide)),
      memStore8_ne (fun e => by have := hs 0 (by decide) 0 (by decide); rw [add_ofNat_zero, add_ofNat_zero] at this; exact this e.symm),
      fR x hx]


end C3.RV32.Sv
