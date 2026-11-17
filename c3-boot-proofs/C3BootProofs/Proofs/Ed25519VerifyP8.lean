import C3BootProofs.Proofs.Ed25519VerifyP7
import C3BootProofs.Proofs.Ed25519VerifyWrap5

/-!
# `ed25519_verify`, offsets 0x189C to 0x19D4: compress and compare

The loop's projective point becomes an extended one, which `compress`
turns into 32 bytes: `y / z` with the sign of `x / z` in the top bit. Those
bytes are compared with the signature's `R`, and the result goes to the
epilogue at 0x100A.
-/

namespace C3.RV32

open C3.Image

/-- `r.as_extended().compress()` for the projective point `r`, as bytes. -/
def evCompress (r : List Nat × List Nat × List Nat) : List Nat :=
  let Z2 := sqL r.2.2
  let recip := mulL (sqIter 5 (pw19L Z2)) (pw3L Z2)
  let s := bytesL (mulL (mulL r.2.1 r.2.2) recip)
  s.set 31 (s.getD 31 0 ^^^ 128 * ((bytesL (mulL (mulL r.1 r.2.2) recip)).getD 0 0 % 2))

theorem sign_byte0 : ∀ b : BitVec 8,
    (aluEval .xor (aluEval .sll (BitVec.ofNat 32 0) 0x7) (b.setWidth 32)).extractLsb' 0 8 = BitVec.ofNat 8 (b.toNat ^^^ 0) := by
  decide

theorem sign_byte1 : ∀ b : BitVec 8,
    (aluEval .xor (aluEval .sll (BitVec.ofNat 32 1) 0x7) (b.setWidth 32)).extractLsb' 0 8 =
      BitVec.ofNat 8 (b.toNat ^^^ 128) := by
  decide

theorem sign_byte (b : BitVec 8) (k : Nat) :
    (aluEval .xor (aluEval .sll (BitVec.ofNat 32 (k % 2)) 0x7) (b.setWidth 32)).extractLsb' 0 8 =
      BitVec.ofNat 8 (b.toNat ^^^ 128 * (k % 2)) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [h]; exact sign_byte0 b
  · rw [h]; exact sign_byte1 b

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

theorem fwL (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {d k c : Nat}
    (hf : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) k x 1 → M' x = M x) (h : c + 40 ≤ d)
    (hd : d + k ≤ 0x16A0) : feW M' (F + BitVec.ofNat 32 c) = feW M (F + BitVec.ofNat 32 c) :=
  fwB fun j hj => hf _ (C.zF (by omega)) (C.offs (Or.inr (by omega)) hd (by omega))

theorem fwR (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {d k c : Nat}
    (hf : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) k x 1 → M' x = M x) (h : d + k ≤ c)
    (hc : c + 40 ≤ 0x16A0) : feW M' (F + BitVec.ofNat 32 c) = feW M (F + BitVec.ofNat 32 c) :=
  fwB fun j hj => hf _ (C.zF (by omega)) (C.offs (Or.inl (by omega)) (by omega) (by omega))

theorem fwZ (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {c : Nat}
    (hf : ∀ x, Sep (evG F) 0xA10 x 1 → M' x = M x) (hc : c + 40 ≤ 0x16A0) :
    feW M' (F + BitVec.ofNat 32 c) = feW M (F + BitVec.ofNat 32 c) :=
  fwB fun j hj => hf _ (C.zF (by omega))

theorem bL (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {d k c : Nat}
    (hf : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) k x 1 → M' x = M x) (h : c + 1 ≤ d)
    (hd : d + k ≤ 0x16A0) : M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
  hf _ (C.zF (by omega)) (C.offs (Or.inr h) hd (by omega))

theorem bR (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {d k c : Nat}
    (hf : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) k x 1 → M' x = M x) (h : d + k ≤ c)
    (hc : c + 1 ≤ 0x16A0) : M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
  hf _ (C.zF (by omega)) (C.offs (Or.inl h) (by omega) hc)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **Compress and compare**, from offset 0x189C to the epilogue. -/
theorem ev_p8 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x189C)
    (h18 : reg n 18 = F + BitVec.ofNat 32 0x1418) (h19 : reg n 19 = F + BitVec.ofNat 32 0x1440)
    (h23 : reg n 23 = F + BitVec.ofNat 32 0x1508) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x100A ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 20] → reg n' q = reg n q) ∧
      reg n' a0 = (if evCompress (prAt M (F + BitVec.ofNat 32 0x13F0)) = memBytes M (F + BitVec.ofNat 32 0x1E8) 32
        then 1 else 0) ∧
      ∀ c, c < 0x16A0 → (c < 0x8F0 ∨ 0x1668 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  -- X * Z
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x18AE)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x5A8) :: (.alu .add a0 a0 sp) :: (.lui a1 0x1000) ::
      (.aluImm .add a1 a1 0x3F0) :: (.alu .add a1 a1 sp) :: (.alu .add a2 x0 (19 : Fin 32)) :: [])
    (blockEnd_cons' (off' := 0x189E) ev_at_189c rfl (blockEnd_cons' (off' := 0x18A2) ev_at_189e rfl
      (blockEnd_cons' (off' := 0x18A4) ev_at_18a2 rfl (blockEnd_cons' (off' := 0x18A6) ev_at_18a4 rfl
      (blockEnd_cons' (off' := 0x18AA) ev_at_18a6 rfl (blockEnd_cons' (off' := 0x18AC) ev_at_18aa rfl
      (blockEnd_cons' (off' := 0x18AE) ev_at_18ac rfl rfl)))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k1 : ∀ q : Fin 32, q.val ∈ evKeep → reg n1 q = reg n q := fun q hq => by
    rw [hr1, evb_reg q D.st.zero (by revert hq; revert q; decide)]
  obtain ⟨n2, c2, D2, k2, w2, f2⟩ := D1.feMul C (d := 0x15A8) (e := 0x13F0) (g := 0x1440) ev_at_18ae ev_at_18b2
    (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h19]; exact BitVec.zero_add _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Y * Z
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x18C6)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x5D0) :: (.alu .add (20 : Fin 32) sp a0) :: (.alu .add a0 x0 (20 : Fin 32)) ::
      (.alu .add a1 x0 (18 : Fin 32)) :: (.alu .add a2 x0 (19 : Fin 32)) :: [])
    (blockEnd_cons' (off' := 0x18B8) ev_at_18b6 rfl (blockEnd_cons' (off' := 0x18BC) ev_at_18b8 rfl
      (blockEnd_cons' (off' := 0x18C0) ev_at_18bc rfl (blockEnd_cons' (off' := 0x18C2) ev_at_18c0 rfl
      (blockEnd_cons' (off' := 0x18C4) ev_at_18c2 rfl (blockEnd_cons' (off' := 0x18C6) ev_at_18c4 rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r3_20 : reg n3 20 = F + BitVec.ofNat 32 0x15D0 := by
    rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl
  have k3 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 20 → reg n3 q = reg n q := fun q hq h20 => by
    rw [hr3, evb_reg q D2.st.zero (by revert h20; revert hq; revert q; decide), k2 q hq, k1 q hq]
  obtain ⟨n4, c4, D4, k4, w4, f4⟩ := D3.feMul C (d := 0x15D0) (e := 0x1418) (g := 0x1440) ev_at_18c6 ev_at_18ca
    (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]
        exact (BitVec.zero_add _).trans rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [k2 18 (by decide), k1 18 (by decide), h18]; exact BitVec.zero_add _)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [k2 19 (by decide), k1 19 (by decide), h19]; exact BitVec.zero_add _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Z²
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x18DC)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x5F8) :: (.alu .add (9 : Fin 32) sp a0) :: (.alu .add a0 x0 (9 : Fin 32)) ::
      (.alu .add a1 x0 (19 : Fin 32)) :: [])
    (blockEnd_cons' (off' := 0x18D0) ev_at_18ce rfl (blockEnd_cons' (off' := 0x18D4) ev_at_18d0 rfl
      (blockEnd_cons' (off' := 0x18D8) ev_at_18d4 rfl (blockEnd_cons' (off' := 0x18DA) ev_at_18d8 rfl
      (blockEnd_cons' (off' := 0x18DC) ev_at_18da rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r5_9 : reg n5 9 = F + BitVec.ofNat 32 0x15F8 := by
    rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl
  have k5 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → reg n5 q = reg n4 q := fun q hq h9 => by
    rw [hr5, evb_reg q D4.st.zero (by revert h9; revert hq; revert q; decide)]
  obtain ⟨n6, c6, D6, k6, w6, f6⟩ := D5.feSq C (d := 0x15F8) (e := 0x1440) ev_at_18dc ev_at_18e0
    (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]
        exact (BitVec.zero_add _).trans rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [k4 19 (by decide), k3 19 (by decide) (by decide), h19]; exact BitVec.zero_add _)
    (by decide) (by decide) (by decide) (by decide)
  -- X * Y
  obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x18F6)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x620) :: (.alu .add a0 a0 sp) :: (.lui a1 0x1000) ::
      (.aluImm .add a1 a1 0x3F0) :: (.alu .add a1 a1 sp) :: (.alu .add a2 x0 (18 : Fin 32)) :: [])
    (blockEnd_cons' (off' := 0x18E6) ev_at_18e4 rfl (blockEnd_cons' (off' := 0x18EA) ev_at_18e6 rfl
      (blockEnd_cons' (off' := 0x18EC) ev_at_18ea rfl (blockEnd_cons' (off' := 0x18EE) ev_at_18ec rfl
      (blockEnd_cons' (off' := 0x18F2) ev_at_18ee rfl (blockEnd_cons' (off' := 0x18F4) ev_at_18f2 rfl
      (blockEnd_cons' (off' := 0x18F6) ev_at_18f4 rfl rfl)))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n8, c8, D8, k8, -, f8⟩ := D7.feMul C (d := 0x1620) (e := 0x13F0) (g := 0x1418) ev_at_18f6 ev_at_18fa
    (by decide) (by decide)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [k6 18 (by decide), k5 18 (by decide) (by decide), k4 18 (by decide),
          k3 18 (by decide) (by decide), h18]; exact BitVec.zero_add _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have k8' : ∀ q : Fin 32, q.val ∈ evKeep → reg n8 q = reg n6 q := fun q hq => by
    rw [k8 q hq, hr7, evb_reg q D6.st.zero (by revert hq; revert q; decide)]
  -- pow22501(Z²)
  obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x1910)
    ((.aluImm .add (8 : Fin 32) sp 0x7FF) :: (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x719) ::
      (.aluImm .add a0 sp 0x7FF) :: (.aluImm .add a0 a0 0x6F1) :: (.alu .add a1 x0 (9 : Fin 32)) :: [])
    (blockEnd_cons' (off' := 0x1902) ev_at_18fe rfl (blockEnd_cons' (off' := 0x1906) ev_at_1902 rfl
      (blockEnd_cons' (off' := 0x190A) ev_at_1906 rfl (blockEnd_cons' (off' := 0x190E) ev_at_190a rfl
      (blockEnd_cons' (off' := 0x1910) ev_at_190e rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r9_8 : reg n9 8 = F + BitVec.ofNat 32 0xF18 := by
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D8.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  have k9 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → reg n9 q = reg n8 q := fun q hq h8 => by
    rw [hr9, evb_reg q D8.st.zero (by revert h8; revert hq; revert q; decide)]
  obtain ⟨n10, c10, D10, k10, w10a, w10b, f10⟩ := D9.pow22501 C (d := 0xEF0) (e := 0x15F8) ev_at_1910 ev_at_1914
    (by decide) (by decide)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D8.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [k8' 9 (by decide), k6 9 (by decide), r5_9]; exact BitVec.zero_add _)
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))
  -- pow2k(t19, 5)
  obtain ⟨n11, c11, D11, hr11⟩ := D10.block C (off' := 0x192A)
    ((.aluImm .add a0 sp 0x7FF) :: (.aluImm .add a0 a0 0x1F1) :: (.aluImm .add a1 sp 0x7FF) ::
      (.aluImm .add a1 a1 0x6F1) :: (.aluImm .add a2 x0 0x5) :: [])
    (blockEnd_cons' (off' := 0x191C) ev_at_1918 rfl (blockEnd_cons' (off' := 0x1920) ev_at_191c rfl
      (blockEnd_cons' (off' := 0x1924) ev_at_1920 rfl (blockEnd_cons' (off' := 0x1928) ev_at_1924 rfl
      (blockEnd_cons' (off' := 0x192A) ev_at_1928 rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n12, c12, D12, k12, w12, f12⟩ := D11.pow2k C (d := 0x9F0) (e := 0xEF0) (k := 5) ev_at_192a ev_at_192e
    (by decide) (by decide) (by decide) (by decide)
    (by rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D10.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D10.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D10.st.zero]); try rfl)
    (by decide) (by decide) (by decide) (by decide)
  have k12' : ∀ q : Fin 32, q.val ∈ evKeep → reg n12 q = reg n10 q := fun q hq => by
    rw [k12 q hq, hr11, evb_reg q D10.st.zero (by revert hq; revert q; decide)]
  -- recip = t20 * t3
  obtain ⟨n13, c13, D13, hr13⟩ := D12.block C (off' := 0x1944)
    ((.aluImm .add a0 sp 0x7FF) :: (.aluImm .add a0 a0 0xF1) :: (.aluImm .add a1 sp 0x7FF) ::
      (.aluImm .add a1 a1 0x1F1) :: (.alu .add a2 x0 (8 : Fin 32)) :: [])
    (blockEnd_cons' (off' := 0x1936) ev_at_1932 rfl (blockEnd_cons' (off' := 0x193A) ev_at_1936 rfl
      (blockEnd_cons' (off' := 0x193E) ev_at_193a rfl (blockEnd_cons' (off' := 0x1942) ev_at_193e rfl
      (blockEnd_cons' (off' := 0x1944) ev_at_1942 rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n14, c14, D14, k14, w14, f14⟩ := D13.feMul C (d := 0x8F0) (e := 0x9F0) (g := 0xF18) ev_at_1944 ev_at_1948
    (by decide) (by decide)
    (by rw [hr13]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D12.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr13]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D12.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr13]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [k12' 8 (by decide), k10 8 (by decide), r9_8]; exact BitVec.zero_add _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have k14' : ∀ q : Fin 32, q.val ∈ evKeep → reg n14 q = reg n12 q := fun q hq => by
    rw [k14 q hq, hr13, evb_reg q D12.st.zero (by revert hq; revert q; decide)]
  -- x = X' * recip
  obtain ⟨n15, c15, D15, hr15⟩ := D14.block C (off' := 0x1964)
    ((.aluImm .add a0 sp 0x7FF) :: (.aluImm .add a0 a0 0x6F1) :: (.lui a1 0x1000) :: (.aluImm .add a1 a1 0x5A8) ::
      (.alu .add a1 a1 sp) :: (.aluImm .add a2 sp 0x7FF) :: (.aluImm .add a2 a2 0xF1) :: [])
    (blockEnd_cons' (off' := 0x1950) ev_at_194c rfl (blockEnd_cons' (off' := 0x1954) ev_at_1950 rfl
      (blockEnd_cons' (off' := 0x1956) ev_at_1954 rfl (blockEnd_cons' (off' := 0x195A) ev_at_1956 rfl
      (blockEnd_cons' (off' := 0x195C) ev_at_195a rfl (blockEnd_cons' (off' := 0x1960) ev_at_195c rfl
      (blockEnd_cons' (off' := 0x1964) ev_at_1960 rfl rfl)))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n16, c16, D16, k16, w16, f16⟩ := D15.feMul C (d := 0xEF0) (e := 0x15A8) (g := 0x8F0) ev_at_1964 ev_at_1968
    (by decide) (by decide)
    (by rw [hr15]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D14.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr15]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D14.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr15]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D14.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have k16' : ∀ q : Fin 32, q.val ∈ evKeep → reg n16 q = reg n14 q := fun q hq => by
    rw [k16 q hq, hr15, evb_reg q D14.st.zero (by revert hq; revert q; decide)]
  -- y = Y' * recip
  obtain ⟨n17, c17, D17, hr17⟩ := D16.block C (off' := 0x1980)
    ((.aluImm .add (8 : Fin 32) sp 0x7FF) :: (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x719) ::
      (.aluImm .add a2 sp 0x7FF) :: (.aluImm .add a2 a2 0xF1) :: (.alu .add a0 x0 (8 : Fin 32)) ::
      (.alu .add a1 x0 (20 : Fin 32)) :: [])
    (blockEnd_cons' (off' := 0x1970) ev_at_196c rfl (blockEnd_cons' (off' := 0x1974) ev_at_1970 rfl
      (blockEnd_cons' (off' := 0x1978) ev_at_1974 rfl (blockEnd_cons' (off' := 0x197C) ev_at_1978 rfl
      (blockEnd_cons' (off' := 0x197E) ev_at_197c rfl (blockEnd_cons' (off' := 0x1980) ev_at_197e rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r17_8 : reg n17 8 = F + BitVec.ofNat 32 0xF18 := by
    rw [hr17]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D16.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  have r16_20 : reg n16 20 = F + BitVec.ofNat 32 0x15D0 := by
    rw [k16' 20 (by decide), k14' 20 (by decide), k12' 20 (by decide), k10 20 (by decide), k9 20 (by decide) (by decide),
      k8' 20 (by decide), k6 20 (by decide), k5 20 (by decide) (by decide), k4 20 (by decide), r3_20]
  obtain ⟨n18, c18, D18, k18, w18, f18⟩ := D17.feMul C (d := 0xF18) (e := 0x15D0) (g := 0x8F0) ev_at_1980 ev_at_1984
    (by decide) (by decide)
    (by rw [hr17]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D16.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]
        exact (BitVec.zero_add _).trans (add_sp F rfl))
    (by rw [hr17]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [r16_20]
        exact BitVec.zero_add _)
    (by rw [hr17]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D16.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- to_bytes(y)
  obtain ⟨n19, c19, D19, hr19⟩ := D18.block C (off' := 0x1992)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x648) :: (.alu .add a0 a0 sp) :: (.alu .add a1 x0 (8 : Fin 32)) :: [])
    (blockEnd_cons' (off' := 0x198A) ev_at_1988 rfl (blockEnd_cons' (off' := 0x198E) ev_at_198a rfl
      (blockEnd_cons' (off' := 0x1990) ev_at_198e rfl (blockEnd_cons' (off' := 0x1992) ev_at_1990 rfl rfl))))
    ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k18' : ∀ q : Fin 32, q.val ∈ evKeep → reg n18 q = reg n17 q := fun q hq => k18 q hq
  obtain ⟨n20, c20, D20, k20, w20, f20⟩ := D19.toBytes C (d := 0x1648) (e := 0xF18) ev_at_1992 ev_at_1996
    (by decide) (by decide)
    (by rw [hr19]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D18.hsp]; exact BitVec.add_comm _ _)
    (by rw [hr19]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [k18' 8 (by decide), r17_8]; exact BitVec.zero_add _)
    (by decide) (by decide) (by decide)
  -- is_negative(x)
  obtain ⟨n21, c21, D21, hr21⟩ := D20.block C (off' := 0x19A2)
    ((.aluImm .add a0 sp 0x7FF) :: (.aluImm .add a0 a0 0x6F1) :: [])
    (blockEnd_cons' (off' := 0x199E) ev_at_199a rfl (blockEnd_cons' (off' := 0x19A2) ev_at_199e rfl rfl))
    ⟨trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n22, c22, D22, k22, v22, f22⟩ := D21.isNeg C (e := 0xEF0) ev_at_19a2 ev_at_19a6 (by decide) (by decide)
    (by rw [hr21]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D20.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by decide) (by decide)
  -- the sign bit
  have r22_23 : reg n22 23 = F + BitVec.ofNat 32 0x1508 := by
    rw [k22 23 (by decide), hr21, evb_reg 23 D20.st.zero (by decide), k20 23 (by decide), hr19,
      evb_reg 23 D18.st.zero (by decide), k18' 23 (by decide), hr17, evb_reg 23 D16.st.zero (by decide),
      k16' 23 (by decide), k14' 23 (by decide), k12' 23 (by decide), k10 23 (by decide), k9 23 (by decide) (by decide),
      k8' 23 (by decide), k6 23 (by decide), k5 23 (by decide) (by decide), k4 23 (by decide),
      k3 23 (by decide) (by decide), h23]
  obtain ⟨n23, c23, D23, hr23⟩ := D22.block C (off' := 0x19B2)
    ((.lbu a1 (23 : Fin 32) 0x15F) :: (.aluImm .sll a0 a0 0x7) :: (.alu .xor a0 a0 a1) :: [])
    (blockEnd_cons' (off' := 0x19AE) ev_at_19aa rfl (blockEnd_cons' (off' := 0x19B0) ev_at_19ae rfl
      (blockEnd_cons' (off' := 0x19B2) ev_at_19b0 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have e23 : reg n23 23 = F + BitVec.ofNat 32 0x1508 := by rw [hr23, evb_reg 23 D22.st.zero (by decide), r22_23]
  have va0 : reg n23 a0 = aluEval .xor (aluEval .sll (BitVec.ofNat 32
      ((bytesL (feW n20.mem (F + BitVec.ofNat 32 0xEF0))).getD 0 0 % 2)) 0x7)
      ((n22.mem (F + BitVec.ofNat 32 0x1667)).setWidth 32) := by
    rw [hr23]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v22, r22_23]
    rw [show F + BitVec.ofNat 32 0x1508 + 0x15F = F + BitVec.ofNat 32 0x1667 from add_ofNat_assoc F _ _]
    try rfl
  obtain ⟨n24, d24, D24, k24⟩ := D23.sb C ev_at_19b2 (off' := 0x19B6) rfl (c := 0x1667)
    (by rw [e23]; exact add_ofNat_assoc F _ _) (by decide)
  -- ct_eq(s, R)
  obtain ⟨n25, c25, D25, hr25⟩ := D24.block C (off' := 0x19C0)
    ((.lui a0 0x1000) :: (.aluImm .add a0 a0 0x648) :: (.alu .add a0 a0 sp) :: (.aluImm .add a1 sp 0x1E8) :: [])
    (blockEnd_cons' (off' := 0x19B8) ev_at_19b6 rfl (blockEnd_cons' (off' := 0x19BC) ev_at_19b8 rfl
      (blockEnd_cons' (off' := 0x19BE) ev_at_19bc rfl (blockEnd_cons' (off' := 0x19C0) ev_at_19be rfl rfl))))
    ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n26, c26, D26, k26, v26, f26⟩ := D25.ctEqSlice C (p := F + BitVec.ofNat 32 0x1648)
    (q := F + BitVec.ofNat 32 0x1E8) ev_at_19c0 ev_at_19c4 (by decide) (by decide)
    (by rw [hr25]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [k24, D23.hsp]
        exact BitVec.add_comm _ _)
    (by rw [hr25]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [k24, D23.hsp]; rfl)
    (C.zF (by decide)).symm (C.zF (by decide)).symm
  obtain ⟨n27, c27, D27, hr27⟩ := D26.block C (off' := 0x19D0)
    ((.aluImm .and a0 a0 0xFF) :: (.alu .sltu a0 x0 a0) :: [])
    (blockEnd_cons' (off' := 0x19CC) ev_at_19c8 rfl (blockEnd_cons' (off' := 0x19D0) ev_at_19cc rfl rfl))
    ⟨trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n28, d28, u28⟩ := D27.st.jump (D27.code C) ev_at_19d0 (off' := 0x100A) (by decide) (by rw [D27.st.pc]; decide)
  -- values
  have pX : prAt M (F + BitVec.ofNat 32 0x13F0) = (feW M (F + BitVec.ofNat 32 0x13F0), feW M (F + BitVec.ofNat 32 0x1418),
      feW M (F + BitVec.ofNat 32 0x1440)) := by
    unfold prAt; rw [add_ofNat_assoc, add_ofNat_assoc]
  have V4 : feW n4.mem (F + BitVec.ofNat 32 0x15D0) =
      mulL (feW M (F + BitVec.ofNat 32 0x1418)) (feW M (F + BitVec.ofNat 32 0x1440)) := by
    rw [w4, fwL C f2 (c := 0x1418) (by decide) (by decide), fwL C f2 (c := 0x1440) (by decide) (by decide)]
  have V6 : feW n6.mem (F + BitVec.ofNat 32 0x15F8) = sqL (feW M (F + BitVec.ofNat 32 0x1440)) := by
    rw [w6, fwL C f4 (c := 0x1440) (by decide) (by decide), fwL C f2 (c := 0x1440) (by decide) (by decide)]
  rw [fwL C f8 (c := 0x15F8) (by decide) (by decide), V6] at w10a w10b
  rw [show (0xEF0 + 40 : Nat) = 0xF18 from rfl] at w10b
  have V14 : feW n14.mem (F + BitVec.ofNat 32 0x8F0) = mulL (sqIter 5 (pw19L (sqL (feW M (F + BitVec.ofNat 32 0x1440)))))
      (pw3L (sqL (feW M (F + BitVec.ofNat 32 0x1440)))) := by
    rw [w14, w12, fwR C f12 (c := 0xF18) (by decide) (by decide), w10a, w10b]
  have V16 : feW n16.mem (F + BitVec.ofNat 32 0xEF0) = mulL (mulL (feW M (F + BitVec.ofNat 32 0x13F0))
      (feW M (F + BitVec.ofNat 32 0x1440))) (mulL (sqIter 5 (pw19L (sqL (feW M (F + BitVec.ofNat 32 0x1440)))))
      (pw3L (sqL (feW M (F + BitVec.ofNat 32 0x1440))))) := by
    rw [w16, fwR C f14 (c := 0x15A8) (by decide) (by decide), fwR C f12 (c := 0x15A8) (by decide) (by decide),
      fwR C f10 (c := 0x15A8) (by decide) (by decide), fwL C f8 (c := 0x15A8) (by decide) (by decide),
      fwL C f6 (c := 0x15A8) (by decide) (by decide), fwL C f4 (c := 0x15A8) (by decide) (by decide), w2, V14]
  have V18 : feW n18.mem (F + BitVec.ofNat 32 0xF18) = mulL (mulL (feW M (F + BitVec.ofNat 32 0x1418))
      (feW M (F + BitVec.ofNat 32 0x1440))) (mulL (sqIter 5 (pw19L (sqL (feW M (F + BitVec.ofNat 32 0x1440)))))
      (pw3L (sqL (feW M (F + BitVec.ofNat 32 0x1440))))) := by
    rw [w18, fwR C f16 (c := 0x15D0) (by decide) (by decide), fwR C f14 (c := 0x15D0) (by decide) (by decide),
      fwR C f12 (c := 0x15D0) (by decide) (by decide), fwR C f10 (c := 0x15D0) (by decide) (by decide),
      fwL C f8 (c := 0x15D0) (by decide) (by decide), fwL C f6 (c := 0x15D0) (by decide) (by decide), V4,
      fwL C f16 (c := 0x8F0) (by decide) (by decide), V14]
  have VX : feW n20.mem (F + BitVec.ofNat 32 0xEF0) = mulL (mulL (feW M (F + BitVec.ofNat 32 0x13F0))
      (feW M (F + BitVec.ofNat 32 0x1440))) (mulL (sqIter 5 (pw19L (sqL (feW M (F + BitVec.ofNat 32 0x1440)))))
      (pw3L (sqL (feW M (F + BitVec.ofNat 32 0x1440))))) := by
    rw [fwL C f20 (c := 0xEF0) (by decide) (by decide), fwL C f18 (c := 0xEF0) (by decide) (by decide), V16]
  -- memory
  have fall24 : ∀ c, c < 0x16A0 → (c < 0x8F0 ∨ 0x1668 ≤ c) →
      memStore8 n22.mem (F + BitVec.ofNat 32 0x1667) ((reg n23 a0).extractLsb' 0 8) (F + BitVec.ofNat 32 c) =
        M (F + BitVec.ofNat 32 c) := fun c hc hh => by
    rcases hh with hh | hh
    · rw [st8_frame (C.offs (Or.inr (by omega)) (by decide) (by omega)), f22 _ (C.zF (by omega)),
        bL C f20 (c := c) (by omega) (by decide), bL C f18 (c := c) (by omega) (by decide),
        bL C f16 (c := c) (by omega) (by decide), bL C f14 (c := c) (by omega) (by decide),
        bL C f12 (c := c) (by omega) (by decide), bL C f10 (c := c) (by omega) (by decide),
        bL C f8 (c := c) (by omega) (by decide), bL C f6 (c := c) (by omega) (by decide),
        bL C f4 (c := c) (by omega) (by decide), bL C f2 (c := c) (by omega) (by decide)]
    · rw [st8_frame (C.offs (Or.inl (by omega)) (by decide) (by omega)), f22 _ (C.zF (by omega)),
        bR C f20 (c := c) (by omega) (by omega), bR C f18 (c := c) (by omega) (by omega),
        bR C f16 (c := c) (by omega) (by omega), bR C f14 (c := c) (by omega) (by omega),
        bR C f12 (c := c) (by omega) (by omega), bR C f10 (c := c) (by omega) (by omega),
        bR C f8 (c := c) (by omega) (by omega), bR C f6 (c := c) (by omega) (by omega),
        bR C f4 (c := c) (by omega) (by omega), bR C f2 (c := c) (by omega) (by omega)]
  have memR : memBytes (memStore8 n22.mem (F + BitVec.ofNat 32 0x1667) ((reg n23 a0).extractLsb' 0 8))
      (F + BitVec.ofNat 32 0x1E8) 32 = memBytes M (F + BitVec.ofNat 32 0x1E8) 32 :=
    memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact fall24 _ (by omega) (Or.inl (by omega))
  have hv : (reg n23 a0).extractLsb' 0 8 = BitVec.ofNat 8 ((n22.mem (F + BitVec.ofNat 32 0x1667)).toNat ^^^
      128 * ((bytesL (feW n20.mem (F + BitVec.ofNat 32 0xEF0))).getD 0 0 % 2)) := by
    rw [va0]; exact sign_byte _ _
  have m22 : memBytes n22.mem (F + BitVec.ofNat 32 0x1648) 32 = memBytes n20.mem (F + BitVec.ofNat 32 0x1648) 32 :=
    memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact f22 _ (C.zF (by omega))
  have byte31 : (n22.mem (F + BitVec.ofNat 32 0x1667)).toNat = (memBytes n22.mem (F + BitVec.ofNat 32 0x1648) 32).getD 31 0 := by
    rw [memBytes_getD (by decide), add_ofNat_assoc]
  have comp : memBytes (memStore8 n22.mem (F + BitVec.ofNat 32 0x1667) ((reg n23 a0).extractLsb' 0 8))
      (F + BitVec.ofNat 32 0x1648) 32 = evCompress (prAt M (F + BitVec.ofNat 32 0x13F0)) := by
    rw [show F + BitVec.ofNat 32 0x1667 = F + BitVec.ofNat 32 0x1648 + BitVec.ofNat 32 31 from (add_ofNat_assoc F 0x1648 31).symm,
      memBytes_set _ _ _ (by decide) (by decide), hv, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 8) (n22.mem _).isLt
        (by have := Nat.mod_lt ((bytesL (feW n20.mem (F + BitVec.ofNat 32 0xEF0))).getD 0 0) (show 2 > 0 by decide)
            show _ < 256; omega)), byte31, m22, w20, V18, VX, pX]
    rfl
  rw [comp, memR] at v26
  refine ⟨n28, n26.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans (c19.trans
    (c20.trans (c21.trans (c22.trans (c23.trans ((Steps.single d24).trans (c25.trans (c26.trans (c27.trans
    (Steps.single d28))))))))))))))))))))))))))), D27.jmp u28, fun q hq hn => ?_, ?_, fun c hc hh => ?_⟩
  · rw [u28.regs, hr27, evb_reg q D26.st.zero (by revert hq; revert q; decide),
      k26 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide),
      hr25, evb_reg q D24.st.zero (by revert hq; revert q; decide), k24, hr23,
      evb_reg q D22.st.zero (by revert hq; revert q; decide), k22 q hq, hr21,
      evb_reg q D20.st.zero (by revert hq; revert q; decide), k20 q hq, hr19,
      evb_reg q D18.st.zero (by revert hq; revert q; decide), k18' q hq, hr17,
      evb_reg q D16.st.zero (by revert hn; revert hq; revert q; decide), k16' q hq, k14' q hq, k12' q hq, k10 q hq,
      k9 q hq (by revert hn; revert hq; revert q; decide), k8' q hq, k6 q hq,
      k5 q hq (by revert hn; revert hq; revert q; decide), k4 q hq,
      k3 q hq (by revert hn; revert hq; revert q; decide)]
  · rw [u28.regs, hr27]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v26]
    by_cases e : evCompress (prAt M (F + BitVec.ofNat 32 0x13F0)) = memBytes M (F + BitVec.ofNat 32 0x1E8) 32
    · rw [if_pos e]; rfl
    · rw [if_neg e]; rfl
  · rw [f26 _ (C.zF (by omega)), fall24 c hc hh]

end

end C3.RV32


