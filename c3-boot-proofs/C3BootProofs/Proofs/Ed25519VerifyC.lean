import C3BootProofs.Proofs.Ed25519VerifyB

/-!
# `ed25519_verify`, as compiled

`evSpec` is what the function computes from its inputs: the checks of
`evSpecA`, then `[k](-A) + [s]B` by the double-base NAF loop, compressed,
and compared with `R`, where `k` is the challenge scalar of
`sha512 (R ‖ A ‖ M)`. `ed25519Verify_correct` runs the machine code from its
entry to its return and shows it returns `evSpec` in `a0`, restores the saved
registers and `sp`, and leaves memory outside its stack as it was.
-/

namespace C3.RV32

open C3.Image

/-- The 40 bytes of a field element that are all zero. -/
def feZ : List Nat := feW (fun _ => 0) 0

/-- **The verification `ed25519_verify` computes**, from the 32-byte key at
`pk`, the 64-byte signature at `sig`, and the `len`-byte message at `msg`. -/
def evSpec (M0 : Word → BitVec 8) (pk sig msg : Word) (len : Nat) : Bool :=
  match evSpecA M0 pk sig with
  | none => false
  | some (X, Y, Z, T) =>
    let k := kOf (smmIn M0 (BitVec.ofNat 32 0x3FCC49E4)) (smmIn M0 (BitVec.ofNat 32 0x3FCC49C0))
      (sha512 (memBytes M0 sig 32 ++ memBytes M0 pk 32 ++ memBytes M0 msg len))
    let aN := nafSpec (leL k 0 32)
    let bN := nafSpec (leL (memBytes M0 (sig + BitVec.ofNat 32 32) 32) 0 32)
    let TA := nafTab (negL X, Y, Z, negL T) (feW M0 apnD)
    let TB := nafTab (ptAt M0 (BitVec.ofNat 32 0x3FCC4A54)) (feW M0 apnD)
    let one := feW M0 (BitVec.ofNat 32 0x3FCC4948)
    decide (evCompress (ladder TA TB aN bN (nafTop aN bN 256 + 1) (feZ, one, one)) = memBytes M0 sig 32)

set_option maxRecDepth 20000 in
theorem nafScalar_leL (M : Word → BitVec 8) (s : Word) : nafScalar M s = leL (memBytes M s 32) 0 32 := by
  unfold nafScalar
  simp only [memLoad32_toNat, le32, leL]
  simp only [memBytes_getD (show 0 + 0 < 32 by decide), memBytes_getD (show 0 + 1 < 32 by decide),
    memBytes_getD (show 0 + 2 < 32 by decide), memBytes_getD (show 0 + 3 < 32 by decide),
    memBytes_getD (show 0 + 4 < 32 by decide), memBytes_getD (show 0 + 5 < 32 by decide),
    memBytes_getD (show 0 + 6 < 32 by decide), memBytes_getD (show 0 + 7 < 32 by decide),
    memBytes_getD (show 0 + 8 < 32 by decide), memBytes_getD (show 0 + 9 < 32 by decide),
    memBytes_getD (show 0 + 10 < 32 by decide), memBytes_getD (show 0 + 11 < 32 by decide),
    memBytes_getD (show 0 + 12 < 32 by decide), memBytes_getD (show 0 + 13 < 32 by decide),
    memBytes_getD (show 0 + 14 < 32 by decide), memBytes_getD (show 0 + 15 < 32 by decide),
    memBytes_getD (show 0 + 16 < 32 by decide), memBytes_getD (show 0 + 17 < 32 by decide),
    memBytes_getD (show 0 + 18 < 32 by decide), memBytes_getD (show 0 + 19 < 32 by decide),
    memBytes_getD (show 0 + 20 < 32 by decide), memBytes_getD (show 0 + 21 < 32 by decide),
    memBytes_getD (show 0 + 22 < 32 by decide), memBytes_getD (show 0 + 23 < 32 by decide),
    memBytes_getD (show 0 + 24 < 32 by decide), memBytes_getD (show 0 + 25 < 32 by decide),
    memBytes_getD (show 0 + 26 < 32 by decide), memBytes_getD (show 0 + 27 < 32 by decide),
    memBytes_getD (show 0 + 28 < 32 by decide), memBytes_getD (show 0 + 29 < 32 by decide),
    memBytes_getD (show 0 + 30 < 32 by decide), memBytes_getD (show 0 + 31 < 32 by decide)]
  simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, Nat.reduceAdd, BitVec.add_zero]
  omega

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The double-base multiplication and the comparison**, from offset 0x158E
to the epilogue. -/
theorem ev_stageC (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x158E)
    (h18 : reg n 18 = F + BitVec.ofNat 32 0x7F0) (h23 : reg n 23 = F + BitVec.ofNat 32 0x1508) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x100A ∧
      reg n' a0 = (if evCompress (ladder
          (nafTab (negL (feW M (F + BitVec.ofNat 32 0x600)), feW M (F + BitVec.ofNat 32 0x628),
            feW M (F + BitVec.ofNat 32 0x650), negL (feW M (F + BitVec.ofNat 32 0x678))) (feW M0 apnD))
          (nafTab (ptAt M0 (BitVec.ofNat 32 0x3FCC4A54)) (feW M0 apnD))
          (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520))) (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0)))
          (nafTop (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520))) (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0)))
            256 + 1)
          (feZ, feW M0 (BitVec.ofNat 32 0x3FCC4948), feW M0 (BitVec.ofNat 32 0x3FCC4948))) =
        memBytes M (F + BitVec.ofNat 32 0x1E8) 32 then 1 else 0) := by
  obtain ⟨n1, M1, c1, D1, k1, r9, r21, r20, r22, r18', r19', dA, dB, tA, tB, z0, o1, o2, fr1⟩ := ev_p6 C D h18
  have hi := nafTop_le (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x520))) (nafSpec (nafScalar M (F + BitVec.ofNat 32 0x6C0))) 256
  obtain ⟨n2, M2, c2, D2, k2, w2, f2⟩ := ev_ladder C
    (TA := nafTab (negL (feW M (F + BitVec.ofNat 32 0x600)), feW M (F + BitVec.ofNat 32 0x628),
      feW M (F + BitVec.ofNat 32 0x650), negL (feW M (F + BitVec.ofNat 32 0x678))) (feW M0 apnD))
    (TB := nafTab (ptAt M0 (BitVec.ofNat 32 0x3FCC4A54)) (feW M0 apnD))
    (fun k => nafSpec_range _ k) (fun k => nafSpec_range _ k) _ (by omega) D1 r9 r21 r20 r22 dA dB tA tB
  obtain ⟨n3, M3, c3, D3, -, a03, -⟩ := ev_p8 C D2 (by rw [k2 18 (by decide) (by decide), r18'])
    (by rw [k2 19 (by decide) (by decide), r19'])
    (by rw [k2 23 (by decide) (by decide), k1 23 (by decide) (by decide), h23])
  have p1 : prAt M1 (F + BitVec.ofNat 32 0x13F0) = (feZ, feW M0 (BitVec.ofNat 32 0x3FCC4948),
      feW M0 (BitVec.ofNat 32 0x3FCC4948)) := by
    have z : feW M1 (F + BitVec.ofNat 32 0x13F0) = feZ := feW_eq2 fun i hi => vk_ld2 fun j hj => by
      rw [add_ofNat_assoc, add_ofNat_assoc, z0 _ (by omega)]
    unfold prAt
    rw [add_ofNat_assoc, add_ofNat_assoc, o1, o2, z]
  have eR : memBytes M2 (F + BitVec.ofNat 32 0x1E8) 32 = memBytes M (F + BitVec.ofNat 32 0x1E8) 32 :=
    memBytes_congr fun i hi => by
      rw [add_ofNat_assoc, f2 _ (by omega) (Or.inl (by omega)), fr1 _ (by omega) (Or.inl (by omega))]
  rw [w2, p1, eR] at a03
  exact ⟨n3, M3, c1.trans (c2.trans c3), D3, a03⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`ed25519_verify`, as compiled**: from its entry to its return, it
returns `evSpec` of its inputs, restores `sp`, `gp`, `tp`, and the registers
it saved, and leaves memory outside its stack as it was. -/
theorem ed25519Verify_correct (m : Machine) {F pk sig msg : Word} {len : Nat} (C : EvCtx m.mem F pk sig msg len)
    (hpc : m.pc = EV) (hsp : reg m sp = F + BitVec.ofNat 32 0x16A0) (ha0 : reg m a0 = pk) (ha1 : reg m a1 = msg)
    (ha2 : reg m a2 = BitVec.ofNat 32 len) (ha3 : reg m a3 = sig) (hret : reg m ra &&& ~~~1 = reg m ra) :
    ∃ m', Steps m m' ∧ m'.pc = reg m ra ∧ reg m' sp = reg m sp ∧ (∀ r o, (r, o) ∈ evPs → reg m' r = reg m r) ∧
      reg m' 3 = reg m 3 ∧ reg m' 4 = reg m 4 ∧ reg m' a0 = (if evSpec m.mem pk sig msg len then 1 else 0) ∧
      ∀ x, Sep (evG F) 0x20B0 x 1 → m'.mem x = m.mem x := by
  obtain ⟨n0, Ms, c0, D0, hsl, k0⟩ := ev_pro m C hpc hsp
  obtain ⟨nA, MA, cA, FA, TA⟩ := ev_stageA C D0 (by rw [k0 a0 (by decide) (by decide), ha0])
    (by rw [k0 a1 (by decide) (by decide), ha1]) (by rw [k0 a2 (by decide) (by decide), ha2])
    (by rw [k0 a3 (by decide) (by decide), ha3])
  have fin : ∀ {n : Machine} {M : Word → BitVec 8}, Steps m n → EvSt m.mem Ms F (reg m) M n 0x100A →
      ∃ m', Steps m m' ∧ m'.pc = reg m ra ∧ reg m' sp = reg m sp ∧ (∀ r o, (r, o) ∈ evPs → reg m' r = reg m r) ∧
        reg m' 3 = reg m 3 ∧ reg m' 4 = reg m 4 ∧ reg m' a0 = reg n a0 ∧
        ∀ x, Sep (evG F) 0x20B0 x 1 → m'.mem x = m.mem x := fun {n M} cs D => by
    obtain ⟨m', c', pc', sp', a0', rs', g', t', mem'⟩ := ev_fin C D hsl hret
    exact ⟨m', cs.trans c', pc', by rw [sp', hsp], rs', g', t', a0', fun x hx => by rw [mem', D.agree x hx]⟩
  cases hA : evSpecA m.mem pk sig with
  | none =>
    obtain ⟨DA, a0A⟩ := FA hA
    obtain ⟨m', c', pc', sp', rs', g', t', a0', mem'⟩ := fin (c0.trans cA) DA
    refine ⟨m', c', pc', sp', rs', g', t', ?_, mem'⟩
    rw [a0', a0A]; unfold evSpec; rw [hA]; rfl
  | some P =>
  obtain ⟨X, Y, Z, T⟩ := P
  obtain ⟨DA, r19, r27, mA, kA, pkA, xA, yA, zA, tA, sA1, sA2⟩ := TA X Y Z T hA
  obtain ⟨nB, MB, cB, DB, r18B, r23B, kB, cpA, cpB, frB⟩ := ev_stageB C DA r19 r27 mA kA
  obtain ⟨nC, MC, cC, DC, a0C⟩ := ev_stageC C DB r18B r23B
  obtain ⟨m', c', pc', sp', rs', g', t', a0', mem'⟩ := fin (c0.trans (cA.trans (cB.trans cC))) DC
  refine ⟨m', c', pc', sp', rs', g', t', ?_, mem'⟩
  have coord : ∀ o, o + 40 ≤ 0xC0 → feW MB (F + BitVec.ofNat 32 (0x5E0 + o)) = feW MA (F + BitVec.ofNat 32 (0x128 + o)) :=
    fun o ho => fwB fun j hj => by
      rw [show 0x5E0 + o + j = 0x5E0 + (o + j) by omega, cpA _ (by omega), show 0x128 + (o + j) = 0x128 + o + j by omega]
  have eX : feW MB (F + BitVec.ofNat 32 0x600) = X := by rw [show (0x600 : Nat) = 0x5E0 + 0x20 from rfl, coord _ (by decide)]; exact xA
  have eY : feW MB (F + BitVec.ofNat 32 0x628) = Y := by rw [show (0x628 : Nat) = 0x5E0 + 0x48 from rfl, coord _ (by decide)]; exact yA
  have eZ : feW MB (F + BitVec.ofNat 32 0x650) = Z := by rw [show (0x650 : Nat) = 0x5E0 + 0x70 from rfl, coord _ (by decide)]; exact zA
  have eT : feW MB (F + BitVec.ofNat 32 0x678) = T := by rw [show (0x678 : Nat) = 0x5E0 + 0x98 from rfl, coord _ (by decide)]; exact tA
  have eRA : memBytes MA (F + BitVec.ofNat 32 0x228) 32 = memBytes m.mem sig 32 :=
    memBytes_ext fun i hi => by rw [add_ofNat_assoc, sA2 i (by omega)]
  have eK : nafScalar MB (F + BitVec.ofNat 32 0x520) = leL (kOf (smmIn m.mem (BitVec.ofNat 32 0x3FCC49E4))
      (smmIn m.mem (BitVec.ofNat 32 0x3FCC49C0))
      (sha512 (memBytes m.mem sig 32 ++ memBytes m.mem pk 32 ++ memBytes m.mem msg len))) 0 32 := by
    rw [nafScalar_leL, kB, eRA, pkA]
  have eS : nafScalar MB (F + BitVec.ofNat 32 0x6C0) = leL (memBytes m.mem (sig + BitVec.ofNat 32 32) 32) 0 32 := by
    rw [nafScalar_leL]
    congr 1
    exact memBytes_ext fun i hi => by
      rw [add_ofNat_assoc, add_ofNat_assoc, show 0x6C0 + i = 0x6A0 + (0x20 + i) by omega, cpB _ (by omega),
        sA2 _ (by omega)]
  have eR : memBytes MB (F + BitVec.ofNat 32 0x1E8) 32 = memBytes m.mem sig 32 :=
    memBytes_ext fun i hi => by rw [add_ofNat_assoc, frB _ (by omega), sA1 i (by omega)]
  rw [a0', a0C, eX, eY, eZ, eT, eK, eS, eR]
  unfold evSpec
  rw [hA]
  exact ite_congr (propext decide_eq_true_iff.symm) (fun _ => rfl) (fun _ => rfl)

end

end C3.RV32





