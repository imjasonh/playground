import C3BootProofs.Proofs.TufRoleKeysMetSig

/-!
# `RoleKeys::met`: the signature checks

From 0x22A, `met` checks the decoded signature at `F + 0x48` against the key
in the slot by the slot's tag. Each check ends at 0x314 with `a0` nonzero
only when the signature verifies, or skips the key at 0x2C0.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.P2v C3.RV32.Pv C3.RV32.Sv C3.RV32.P3

set_option maxRecDepth 20000

/-- The registers that the signature checks keep: `sp`, 0x62 in `s2`, the
`RoleKeys` in `s3`, the count in `s4`, `i` and `i + 1` in `s6` and `s7`, the
tag in `s8`, `s9`, and `s10`. -/
abbrev rmSL : List (Fin 32) := [sp, 18, 19, 20, 22, 23, 24, 25, 26]

section
variable {M0 M1 Mz : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word}
  {S : Prop} {H : Post}

theorem rm_n64 : ∀ n, n < 129 → branchTaken .bne (aluEval .add (BitVec.ofNat 32 n) 0xFFFFFFC0) 0 = false →
    n = 64 := by decide

/-- From 0x298, the Ed25519 check: a signature of 64 bytes, verified with
`ed25519Verify` against the 32-byte key at `pk`. -/
theorem rm_ed (E : RmEnv M0 M1 s F R MP SP ML SL g0) {G g : Fin 32 → Word} (hK : ∀ x, x ∈ rmSL → g x = G x)
    (hsp : g sp = F) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) {pk : Word} (h8 : g 8 = pk)
    (hpk : Sep s 0x3920 pk 32) (hpkw : pk.toNat + 32 < 2 ^ 32) {n : Nat} (hn : n ≤ 128)
    (h12 : g 12 = BitVec.ofNat 32 n) (h13 : g 13 = F + BitVec.ofNat 32 0x48)
    {Mk : Word → BitVec 8} (hM : RmVM M1 Mz Mk s F) (hmp : memLoad32 Mz (F + BitVec.ofNat 32 0x14) = MP)
    (hml : memLoad32 Mz (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML)
    (hskip : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x2C0 g')
    (hdone : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → (g' 10 ≠ 0 → n = 64 ∧
        ed25519Verify (memBytes M0 pk 32) (memBytes M0 MP ML) (memBytes Mk (F + BitVec.ofNat 32 0x48) 64) = true) →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x314 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x298 g := by
  have hF48 : F + BitVec.ofNat 32 0x48 = s + BitVec.ofNat 32 0x3778 := E.Fc 0x48
  have hlo := E.hlo
  have hhi := E.hhi
  refine WP.aluImm rkm_at_298 ?_; wn
  refine WP.branch rkm_at_29c (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact hskip Mk _ hM (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0)
  have h64 : n = 64 := rm_n64 n (by omega) (by (try rsimp at eb); rw [h12] at eb; exact eb)
  subst h64
  have C := E.code hM.1
  have hmp' : memLoad32 Mk (F + BitVec.ofNat 32 0x14) = MP := (hM.2.load (c := 8) (by decide)).trans hmp
  have hml' : memLoad32 Mk (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML :=
    (hM.2.load (c := 4) (by decide)).trans hml
  have hFn : (F + BitVec.ofNat 32 0x48).toNat = s.toNat + 0x3730 + 0x48 := E.FN (by decide)
  refine WP.alu rkm_at_29e ?_; wn
  refine WP.lw rkm_at_2a0 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x14) (by decide)) ?_; wn
  refine WP.lw rkm_at_2a2 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x10) (by decide)) ?_; wn
  refine WP.callEdM (F := s + BitVec.ofNat 32 0x2090) (pk := pk) (sig := F + BitVec.ofNat 32 0x48) (msg := MP)
    (len := ML) rkm_at_2a4 rkm_at_2a8 (by decide) (by decide)
    (E.ev C (hpk.sub (c := 0x1680) (l := 0x20B0) (by decide)).symm (by rw [hF48]; exact E.ss (Or.inr (by decide)) (by decide) (by decide))
      (E.hSM.sub (c := 0x1680) (l := 0x20B0) (by decide)).symm hpkw (by omega) E.hMw E.hML) C.edI C.edK
    (by (try rsimp); rw [hsp]; exact E.evF) (by (try rsimp); rw [ev0, h8])
    (by (try rsimp); rw [hsp]; exact hmp') (by (try rsimp); rw [hsp]; exact hml') (by (try rsimp); exact h13)
    (by rw [E.evG]; exact E.lowS (by decide) (by decide) (by decide)) fun m2 hv hO => ?_
  have hM2 : RmVM M1 Mz m2.mem s F := RmVM.one E.toRmBase hM (by rw [← E.evG]; exact hO) (by decide)
  refine WP.jal rkm_at_2ac (by decide) ?_; wn
  refine hdone m2.mem _ hM2 (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0) fun ha => ⟨rfl, ?_⟩
  have hv' := hv (by (try rsimp at ha); exact ha)
  rwa [E.bytes hM.1 hpk, E.bytes hM.1 E.hSM] at hv'

end

end C3.RV32
