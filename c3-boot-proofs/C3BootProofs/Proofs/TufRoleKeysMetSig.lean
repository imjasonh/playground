import C3BootProofs.Proofs.TufRoleKeysMetDup
import C3BootProofs.Proofs.TufRoleKeysMetEnv

/-!
# `RoleKeys::met`: decoding the signature

From 0x20A, `met` clears 128 bytes at `F + 0x48` and hex-decodes the
signature into them. A signature that isn't hex, or that is longer than 256
characters, skips the key at 0x2C0. Otherwise the code goes on at 0x22A with
the decoded bytes at `F + 0x48`.

`RmVM` is the memory that the signature checks keep: memory outside the
stack as before, and the outer loop's words. `RmVM.two` keeps it across a
change in two ranges that miss the outer loop's words and the saved
registers.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.P2v C3.RV32.Pv C3.RV32.Sv C3.RV32.P3

set_option maxRecDepth 20000

/-- The memory that the signature checks keep: memory outside the stack as
in `M1`, and the outer loop's words as in `Mz`. -/
def RmVM (M1 Mz Mk : Word → BitVec 8) (s F : Word) : Prop :=
  Out M1 Mk s 0x38EC ∧ RmLow Mz Mk F

/-- A range of `l` bytes `d` bytes from `s` that misses the outer loop's
words and the saved registers. -/
abbrev RmOk (d l : Nat) : Prop := d + l ≤ 0x373C ∨ (0x3778 ≤ d ∧ d + l ≤ 0x38EC)

section
variable {M0 M1 Mz Ma Mb : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word}
  {S : Prop} {H : Post}

theorem RmVM.two (E : RmBase M0 M1 s F R MP SP ML SL g0) (h : RmVM M1 Mz Ma s F) {d1 l1 d2 l2 : Nat}
    (hO : ∀ x, Sep x 1 (s + BitVec.ofNat 32 d1) l1 → Sep x 1 (s + BitVec.ofNat 32 d2) l2 → Mb x = Ma x)
    (h1 : RmOk d1 l1) (h2 : RmOk d2 l2) : RmVM M1 Mz Mb s F := by
  have hs : ∀ {d l : Nat}, RmOk d l → ∀ j, j < 0x3C →
      Sep (F + BitVec.ofNat 32 0xC + BitVec.ofNat 32 j) 1 (s + BitVec.ofNat 32 d) l := by
    intro d l hd j hj
    have := E.fs (c := 0xC + j) (n := 1) (d := d) (k := l) (by omega) (by omega) (by omega)
    rw [← add_ofNat_assoc] at this; exact this
  refine ⟨fun x hx => (hO x (sep_in hx (by omega)) (sep_in hx (by omega))).trans (h.1 x hx), fun j hj => ?_⟩
  exact (hO _ (hs h1 j hj) (hs h2 j hj)).trans (h.2 j hj)

theorem RmVM.one (E : RmBase M0 M1 s F R MP SP ML SL g0) (h : RmVM M1 Mz Ma s F) {d l : Nat}
    (hO : Out Ma Mb (s + BitVec.ofNat 32 d) l) (hd : RmOk d l) : RmVM M1 Mz Mb s F :=
  RmVM.two E h (fun x hx _ => hO x hx) hd hd

theorem RmVM.bytes (E : RmBase M0 M1 s F R MP SP ML SL g0) (h : RmVM M1 Mz Ma s F) {q : Word} {l : Nat}
    (hS : Sep s 0x3920 q l) : memBytes Ma q l = memBytes M0 q l :=
  E.bytes h.1 hS

/-- From 0x20A: clear the 128 bytes at `F + 0x48` and hex-decode the
signature, the `l` bytes at `SP + q`, into them. -/
theorem rm_hex (E : RmBase M0 M1 s F R MP SP ML SL g0) {g : Fin 32 → Word} (hsp : g sp = F) (hz : g 0 = 0)
    (hfr : ∀ x, x ∉ rkE → g x = g0 x) {q l : Nat} (h25 : g 25 = SP + BitVec.ofNat 32 q) (hql : q + l ≤ SL)
    {Mk : Word → BitVec 8} (hM : RmVM M1 Mz Mk s F) (h8 : memLoad32 Mk (F + 8) = BitVec.ofNat 32 l)
    (hskip : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmDL → g' x = g x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x2C0 g')
    (hgo : ∀ Mk' g' (bs : Bytes), RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmDL → g' x = g x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → g' 10 = F + BitVec.ofNat 32 0x48 → g' 11 = BitVec.ofNat 32 (l / 2) →
      l ≤ 256 → parseHex (memBytes M0 (SP + BitVec.ofNat 32 q) l) = some bs → bs.length = l / 2 →
      memBytes Mk' (F + BitVec.ofNat 32 0x48) (l / 2) = bs →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x22A g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x20A g := by
  have hc := E.codeA hM.1
  have hE := fun x (_ : x ∈ rmDL) => (rfl : g x = g x)
  have hSL := E.hSL
  have hF48 : F + BitVec.ofNat 32 0x48 = s + BitVec.ofNat 32 0x3778 := E.Fc 0x48
  refine WP.aluImm rkm_at_20a ?_; wn
  refine WP.aluImm rkm_at_20c ?_; wn
  refine WP.aluImm rkm_at_210 ?_; wn
  refine WP.callMemsetT (tb := TPS_MS) (dst := F + BitVec.ofNat 32 0x48) (b := 0) (n := 0x80) rkm_at_212
    rkm_at_216 (by decide) (by decide) (by decide) hc.rk.tps.ms (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); try (rw [hz]; rfl)) (by (try rsimp); try rfl) (by have := E.wF (c := 0x48) (k := 0x80) (by decide); omega)
    (E.lowF (by decide) (by decide) (by decide)) (E.cF (by decide)) fun m2 hm2 => ?_
  have oF : Out Mk m2.mem (F + BitVec.ofNat 32 0x48) 0x80 := fun x hx => by
    rw [hm2]; exact fillBytes_sep hx.symm (Nat.le_refl _)
  have h82 : memLoad32 m2.mem (F + 8) = BitVec.ofNat 32 l := by
    rw [← h8]
    exact oF.load32 (rm_ff F (c := 0x48) (n := 0x80) (d := 8) (k := 4) (Or.inr (by decide)) (by decide) (by decide))
  have hM2 : RmVM M1 Mz m2.mem s F := RmVM.one E hM (by rw [← hF48]; exact oF) (by decide)
  clear hm2 oF
  generalize m2.mem = M2 at hM2 h82
  have hc2 := E.codeA hM2.1
  have hSq : Sep s 0x3920 (SP + BitVec.ofNat 32 q) l := E.hSS.subR hql
  have hr : F + 0xFFFFFFE0 = s + BitVec.ofNat 32 0x3710 := E.Fm (c := 32) (by decide) rfl
  refine WP.aluImm rkm_at_21a ?_; wn
  refine WP.alu rkm_at_21c ?_; wn
  refine WP.lw rkm_at_21e (by (try rsimp); rw [hsp]; exact E.alF (c := 8) (by decide)) ?_; wn
  refine WP.callHex (text := SP + BitVec.ofNat 32 q) (out := F + BitVec.ofNat 32 0x48) (r := F + 0xFFFFFFE0)
    (len := l) rkm_at_220 rkm_at_224 (by decide) (by decide) hc2.rk.hex hc2.rk.hv
    (by (try rsimp); rw [ev0]; exact h25) (by (try rsimp); rw [hsp]; exact h82) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by omega) (by (try rsimp); rw [hsp]) (by (try rsimp); rw [hsp]; have := E.halF; omega)
    (by rw [hr]; exact E.lowS (by decide) (by decide) (by decide))
    (by rw [hr]; exact E.lowS (by decide) (by decide) (by decide))
    (by rw [hr]; exact hSq.sub (by decide))
    (by rw [hr, hF48]; exact E.ss (Or.inl (by decide)) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (by rw [hF48]; exact hSq.sub (by decide))
    (by rw [hr]; exact E.lowS (by decide) (by decide) (by decide)) (E.cF (by decide)) fun m3 r0 r1 rb hmf => ?_
  have hM3 : RmVM M1 Mz m3.mem s F := RmVM.two E hM2 (d1 := 0x3710) (l1 := 32) (d2 := 0x3778) (l2 := 128) (by rw [← hr, ← hF48]; exact hmf) (by decide) (by decide)
  rw [show tufHexDecodeSpec M2 (SP + BitVec.ofNat 32 q) l =
      if l ≤ 256 then parseHex (memBytes M0 (SP + BitVec.ofNat 32 q) l) else none by
    unfold tufHexDecodeSpec; rw [E.bytes hM2.1 hSq]] at r0 rb
  have hFp : (F + BitVec.ofNat 32 0x48).toNat = s.toNat + 0x3778 := E.FN (by decide)
  have hlo := E.hlo
  refine WP.branch rkm_at_228 (fun eb => ?_) (fun eb => ?_) <;> wn
  · by_cases hl : l ≤ 256
    · rw [ite_eq_left hl] at r0
      cases hp : parseHex (memBytes M0 (SP + BitVec.ofNat 32 q) l) with
      | none =>
        exact hskip m3.mem _ hM3 (by rmkeep hE) (by rsimp; (try exact hz)) (by keepz E.hz0)
      | some bs =>
        exfalso; (try rsimp at eb); rw [r0, hp] at eb
        have e0 : F + BitVec.ofNat 32 0x48 = 0 := rm_beqT (a := F + BitVec.ofNat 32 0x48) eb
        have := congrArg BitVec.toNat e0
        rw [hFp] at this; exact absurd this fun h => by have h' : s.toNat + 0x3778 = 0 := h; omega
    · exact hskip m3.mem _ hM3 (by rmkeep hE) (by rsimp; (try exact hz)) (by keepz E.hz0)
  · by_cases hl : l ≤ 256
    · rw [ite_eq_left hl] at r0 rb
      cases hp : parseHex (memBytes M0 (SP + BitVec.ofNat 32 q) l) with
      | none =>
        exfalso; (try rsimp at eb); rw [r0, hp] at eb
        have e1 : branchTaken .beq (0 : Word) 0 = false := eb; exact absurd e1 (by decide)
      | some bs =>
        obtain ⟨hbl, hbm⟩ := rb bs hp
        rw [hp] at r0
        exact hgo m3.mem _ bs hM3 (by rmkeep hE) (by rsimp; (try exact hz)) (by keepz E.hz0)
          (by (try rsimp); exact r0) (by (try rsimp); exact r1) hl hp hbl hbm
    · exfalso; (try rsimp at eb); rw [ite_eq_right hl] at r0; rw [r0] at eb
      have e1 : branchTaken .beq (0 : Word) 0 = false := eb; exact absurd e1 (by decide)

end

end C3.RV32
