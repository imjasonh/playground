import C3BootProofs.Proofs.TufRoleKeysPub

/-!
# `decode_key`'s comparison tree, inlined in `RoleKeys::read`

From 0x37C `RoleKeys::read` compares the scheme and the key type with
`ecdsa-sha2-nistp256`, `ecdsa-sha2-nistp384`, `ecdsa`, and `ed25519`, one
byte at a time, and goes on to the key decode the pair names, or to 0x628,
0x630, or 0x632 without a key. `RkT.t37c` is the whole tree, against
`rkKey`.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

/-! ## The byte-comparison chains -/

theorem rk_ch_3aa : rkChain tufRoleKeysReadCode false 12 0x630 rkP256s 0x3AA 2 1 = some 0x3B6 :=
    (rkChain_cons (.inl rfl) rkr_at_3aa rfl (by decide) rkr_at_3ae (by decide) rfl rkr_at_3b2 (by decide) rfl
    rkChain_nil)

theorem rk_ch_3b6 : rkChain tufRoleKeysReadCode false 12 0x628 rkP256s 0x3B6 3 1 = some 0x3C2 :=
    (rkChain_cons (.inl rfl) rkr_at_3b6 rfl (by decide) rkr_at_3ba (by decide) rfl rkr_at_3be (by decide) rfl
    rkChain_nil)

theorem rk_ch_3c2 : rkChain tufRoleKeysReadCode true 12 0x628 rkP256s 0x3C2 4 12 = some 0x46A :=
    (rkChain_cons (.inr rkr_at_3c2) rkr_at_3c4 rfl (by decide) rkr_at_3c8 (by decide) rfl rkr_at_3cc (by decide) rfl
    (rkChain_cons (.inr rkr_at_3d0) rkr_at_3d2 rfl (by decide) rkr_at_3d6 (by decide) rfl rkr_at_3da (by decide) rfl
    (rkChain_cons (.inr rkr_at_3de) rkr_at_3e0 rfl (by decide) rkr_at_3e4 (by decide) rfl rkr_at_3e8 (by decide) rfl
    (rkChain_cons (.inr rkr_at_3ec) rkr_at_3ee rfl (by decide) rkr_at_3f2 (by decide) rfl rkr_at_3f6 (by decide) rfl
    (rkChain_cons (.inr rkr_at_3fa) rkr_at_3fc rfl (by decide) rkr_at_400 (by decide) rfl rkr_at_404 (by decide) rfl
    (rkChain_cons (.inr rkr_at_408) rkr_at_40a rfl (by decide) rkr_at_40e (by decide) rfl rkr_at_412 (by decide) rfl
    (rkChain_cons (.inr rkr_at_416) rkr_at_418 rfl (by decide) rkr_at_41c (by decide) rfl rkr_at_420 (by decide) rfl
    (rkChain_cons (.inr rkr_at_424) rkr_at_426 rfl (by decide) rkr_at_42a (by decide) rfl rkr_at_42e (by decide) rfl
    (rkChain_cons (.inr rkr_at_432) rkr_at_434 rfl (by decide) rkr_at_438 (by decide) rfl rkr_at_43c (by decide) rfl
    (rkChain_cons (.inr rkr_at_440) rkr_at_442 rfl (by decide) rkr_at_446 (by decide) rfl rkr_at_44a (by decide) rfl
    (rkChain_cons (.inr rkr_at_44e) rkr_at_450 rfl (by decide) rkr_at_454 (by decide) rfl rkr_at_458 (by decide) rfl
    (rkChain_cons (.inr rkr_at_45c) rkr_at_45e rfl (by decide) rkr_at_462 (by decide) rfl rkr_at_466 (by decide) rfl
    rkChain_nil))))))))))))

theorem rk_ch_480 : rkChain tufRoleKeysReadCode true 12 0x628 rkP256s 0x480 17 2 = some 0x49C :=
    (rkChain_cons (.inr rkr_at_480) rkr_at_482 rfl (by decide) rkr_at_486 (by decide) rfl rkr_at_48a (by decide) rfl
    (rkChain_cons (.inr rkr_at_48e) rkr_at_490 rfl (by decide) rkr_at_494 (by decide) rfl rkr_at_498 (by decide) rfl
    rkChain_nil))

theorem rk_ch_636 : rkChain tufRoleKeysReadCode true 12 0x628 rkP384s 0x636 17 2 = some 0x64E :=
    (rkChain_cons (.inr rkr_at_636) rkr_at_638 rfl (by decide) rkr_at_63c (by decide) rfl rkr_at_640 (by decide) rfl
    (rkChain_cons (.inr rkr_at_642) rkr_at_644 rfl (by decide) rkr_at_648 (by decide) rfl rkr_at_64c (by decide) rfl
    rkChain_nil))

theorem rk_ch_71c : rkChain tufRoleKeysReadCode false 23 0x628 rkP256s 0x71C 0 18 = some 0x7F2 :=
    (rkChain_cons (.inl rfl) rkr_at_71c rfl (by decide) rkr_at_720 (by decide) rfl rkr_at_724 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_726 rfl (by decide) rkr_at_72a (by decide) rfl rkr_at_72e (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_732 rfl (by decide) rkr_at_736 (by decide) rfl rkr_at_73a (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_73e rfl (by decide) rkr_at_742 (by decide) rfl rkr_at_746 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_74a rfl (by decide) rkr_at_74e (by decide) rfl rkr_at_752 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_756 rfl (by decide) rkr_at_75a (by decide) rfl rkr_at_75e (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_762 rfl (by decide) rkr_at_766 (by decide) rfl rkr_at_76a (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_76e rfl (by decide) rkr_at_772 (by decide) rfl rkr_at_776 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_77a rfl (by decide) rkr_at_77e (by decide) rfl rkr_at_782 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_786 rfl (by decide) rkr_at_78a (by decide) rfl rkr_at_78e (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_792 rfl (by decide) rkr_at_796 (by decide) rfl rkr_at_79a (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_79e rfl (by decide) rkr_at_7a2 (by decide) rfl rkr_at_7a6 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_7aa rfl (by decide) rkr_at_7ae (by decide) rfl rkr_at_7b2 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_7b6 rfl (by decide) rkr_at_7ba (by decide) rfl rkr_at_7be (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_7c2 rfl (by decide) rkr_at_7c6 (by decide) rfl rkr_at_7ca (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_7ce rfl (by decide) rkr_at_7d2 (by decide) rfl rkr_at_7d6 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_7da rfl (by decide) rkr_at_7de (by decide) rfl rkr_at_7e2 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_7e6 rfl (by decide) rkr_at_7ea (by decide) rfl rkr_at_7ee (by decide) rfl
    rkChain_nil))))))))))))))))))

theorem rk_ch_4ac : rkChain tufRoleKeysReadCode false 23 0x628 rkEcdsa 0x4AC 0 4 = some 0x4DC :=
    (rkChain_cons (.inl rfl) rkr_at_4ac rfl (by decide) rkr_at_4b0 (by decide) rfl rkr_at_4b4 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_4b8 rfl (by decide) rkr_at_4bc (by decide) rfl rkr_at_4c0 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_4c4 rfl (by decide) rkr_at_4c8 (by decide) rfl rkr_at_4cc (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_4d0 rfl (by decide) rkr_at_4d4 (by decide) rfl rkr_at_4d8 (by decide) rfl
    rkChain_nil))))

theorem rk_ch_7fc : rkChain tufRoleKeysReadCode false 23 0x628 rkP384s 0x7FC 0 18 = some 0x8D4 :=
    (rkChain_cons (.inl rfl) rkr_at_7fc rfl (by decide) rkr_at_800 (by decide) rfl rkr_at_804 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_808 rfl (by decide) rkr_at_80c (by decide) rfl rkr_at_810 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_814 rfl (by decide) rkr_at_818 (by decide) rfl rkr_at_81c (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_820 rfl (by decide) rkr_at_824 (by decide) rfl rkr_at_828 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_82c rfl (by decide) rkr_at_830 (by decide) rfl rkr_at_834 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_838 rfl (by decide) rkr_at_83c (by decide) rfl rkr_at_840 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_844 rfl (by decide) rkr_at_848 (by decide) rfl rkr_at_84c (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_850 rfl (by decide) rkr_at_854 (by decide) rfl rkr_at_858 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_85c rfl (by decide) rkr_at_860 (by decide) rfl rkr_at_864 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_868 rfl (by decide) rkr_at_86c (by decide) rfl rkr_at_870 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_874 rfl (by decide) rkr_at_878 (by decide) rfl rkr_at_87c (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_880 rfl (by decide) rkr_at_884 (by decide) rfl rkr_at_888 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_88c rfl (by decide) rkr_at_890 (by decide) rfl rkr_at_894 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_898 rfl (by decide) rkr_at_89c (by decide) rfl rkr_at_8a0 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_8a4 rfl (by decide) rkr_at_8a8 (by decide) rfl rkr_at_8ac (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_8b0 rfl (by decide) rkr_at_8b4 (by decide) rfl rkr_at_8b8 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_8bc rfl (by decide) rkr_at_8c0 (by decide) rfl rkr_at_8c4 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_8c8 rfl (by decide) rkr_at_8cc (by decide) rfl rkr_at_8d0 (by decide) rfl
    rkChain_nil))))))))))))))))))

theorem rk_ch_65e : rkChain tufRoleKeysReadCode false 23 0x628 rkEcdsa 0x65E 0 4 = some 0x686 :=
    (rkChain_cons (.inl rfl) rkr_at_65e rfl (by decide) rkr_at_662 (by decide) rfl rkr_at_666 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_668 rfl (by decide) rkr_at_66c (by decide) rfl rkr_at_670 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_672 rfl (by decide) rkr_at_676 (by decide) rfl rkr_at_67a (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_67c rfl (by decide) rkr_at_680 (by decide) rfl rkr_at_684 (by decide) rfl
    rkChain_nil))))

theorem rk_ch_558 : rkChain tufRoleKeysReadCode false 23 0x628 rkEd 0x558 0 7 = some 0x59E :=
    (rkChain_cons (.inl rfl) rkr_at_558 rfl (by decide) rkr_at_55c (by decide) rfl rkr_at_560 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_562 rfl (by decide) rkr_at_566 (by decide) rfl rkr_at_56a (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_56c rfl (by decide) rkr_at_570 (by decide) rfl rkr_at_574 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_576 rfl (by decide) rkr_at_57a (by decide) rfl rkr_at_57e (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_580 rfl (by decide) rkr_at_584 (by decide) rfl rkr_at_588 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_58a rfl (by decide) rkr_at_58e (by decide) rfl rkr_at_592 (by decide) rfl
    (rkChain_cons (.inl rfl) rkr_at_594 rfl (by decide) rkr_at_598 (by decide) rfl rkr_at_59c (by decide) rfl
    rkChain_nil)))))))

theorem rk_ch_59e : rkChain tufRoleKeysReadCode true 12 0x628 rkEd 0x59E 0 6 = some 0x5E6 :=
    (rkChain_cons (.inr rkr_at_59e) rkr_at_5a0 rfl (by decide) rkr_at_5a4 (by decide) rfl rkr_at_5a8 (by decide) rfl
    (rkChain_cons (.inr rkr_at_5aa) rkr_at_5ac rfl (by decide) rkr_at_5b0 (by decide) rfl rkr_at_5b4 (by decide) rfl
    (rkChain_cons (.inr rkr_at_5b6) rkr_at_5b8 rfl (by decide) rkr_at_5bc (by decide) rfl rkr_at_5c0 (by decide) rfl
    (rkChain_cons (.inr rkr_at_5c2) rkr_at_5c4 rfl (by decide) rkr_at_5c8 (by decide) rfl rkr_at_5cc (by decide) rfl
    (rkChain_cons (.inr rkr_at_5ce) rkr_at_5d0 rfl (by decide) rkr_at_5d4 (by decide) rfl rkr_at_5d8 (by decide) rfl
    (rkChain_cons (.inr rkr_at_5da) rkr_at_5dc rfl (by decide) rkr_at_5e0 (by decide) rfl rkr_at_5e4 (by decide) rfl
    rkChain_nil))))))

/-! ## The state the tree reads -/

theorem rk_byte0 {b : BitVec 8} {c : Word} {n : Nat} (hn : n < 256) (hc : c + BitVec.ofNat 32 n = 0) :
    b.zeroExtend 32 + c = 0 ↔ b = BitVec.ofNat 8 n := by
  constructor
  · intro h0
    have e : b.zeroExtend 32 = BitVec.ofNat 32 n :=
      calc b.zeroExtend 32 = b.zeroExtend 32 + (c + BitVec.ofNat 32 n) := by rw [hc]; exact (BitVec.add_zero _).symm
        _ = (b.zeroExtend 32 + c) + BitVec.ofNat 32 n := (BitVec.add_assoc ..).symm
        _ = BitVec.ofNat 32 n := by rw [h0]; exact BitVec.zero_add _
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega),
      Nat.mod_eq_of_lt (by omega)] at this
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  · intro e; subst e
    rw [← hc, BitVec.add_comm c]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega

theorem rk_getD_lt {L : Bytes} (hLb : ∀ x ∈ L, x < 256) (j : Nat) : L.getD j 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hh : L[j]? with _ | x
  · decide
  · exact hLb x (List.mem_of_getElem? hh)

/-- With all but the last byte of `L` at `q`, the last byte decides whether
the `n` bytes there are `L`. -/
theorem rk_last {M : Word → BitVec 8} {q : Word} {n : Nat} {L kt : Bytes} (hkt : memBytes M q n = kt)
    (hp : RkPre M q L (n - 1)) (hn : L.length = n) (h0 : 0 < n) (hLb : ∀ x ∈ L, x < 256) :
    M (q + BitVec.ofNat 32 (n - 1)) = BitVec.ofNat 8 (L.getD (n - 1) 0) ↔ kt = L := by
  constructor
  · intro hb
    have := hp.snoc hb
    rw [show n - 1 + 1 = n by omega] at this
    rw [← hkt]; exact this.eq hn hLb
  · intro e
    rcases Decidable.em (M (q + BitVec.ofNat 32 (n - 1)) = BitVec.ofNat 8 (L.getD (n - 1) 0)) with h | h
    · exact h
    · exact absurd e (rk_ne hkt (by omega) h)

/-- The last compare, `lbu a1, n-1(q); addi a1, a1, c`, is zero exactly
when the `n` bytes at `q` are `L`. -/
theorem rk_lastb {M : Word → BitVec 8} {q : Word} {n : Nat} {L kt : Bytes} {c : Word} (hkt : memBytes M q n = kt)
    (hp : RkPre M q L (n - 1)) (hn : L.length = n) (h0 : 0 < n) (hLb : ∀ x ∈ L, x < 256)
    (hc : c + BitVec.ofNat 32 (L.getD (n - 1) 0) = 0) :
    aluEval .add ((M (q + BitVec.ofNat 32 (n - 1))).zeroExtend 32) c = 0 ↔ kt = L := by
  rw [ev_add, rk_byte0 (rk_getD_lt hLb _) hc, rk_last hkt hp hn h0 hLb]

theorem rk_bneT {a b : Word} (h : branchTaken .bne a b = true) : a ≠ b := by
  simpa [branchTaken] using h

theorem rk_beqT {a b : Word} (h : branchTaken .beq a b = true) : a = b := by
  simpa [branchTaken] using h

theorem rk_beqF {a b : Word} (h : branchTaken .beq a b = false) : a ≠ b := by
  simpa [branchTaken] using h

theorem rk_p384_pfx : ∀ j < 16, rkP256s.getD j 0 = rkP384s.getD j 0 := by decide

theorem rk_p384_pfx' : ∀ j < 16, rkP384s.getD j 0 = rkP256s.getD j 0 := by decide

theorem rkP256s_b : ∀ x ∈ rkP256s, x < 256 := by decide
theorem rkP384s_b : ∀ x ∈ rkP384s, x < 256 := by decide
theorem rkEcdsa_b : ∀ x ∈ rkEcdsa, x < 256 := by decide
theorem rkEd_b : ∀ x ∈ rkEd, x < 256 := by decide

/-- What the tree reads: the key type `kt` at `ktq`, the scheme `sc` at
`scq` and its pointer and length in the frame, and the public key text
`pub`, the `pl` bytes at `pq`. -/
structure RkT (M0 M1 Md M : Word → BitVec 8) (s out F P : Word) (N : Nat) (g0 gL : Fin 32 → Word) (Q : Post)
    (kt sc pub : Bytes) (ktq scq pq : Word) (pl : Nat) : Prop where
  E : RkEnv M0 M1 s out F P N g0
  hOd : Out M1 Md s 3004
  hW : RkW s Md M
  hL0 : gL 0 = 0
  hLsp : gL sp = F
  hL24 : gL 24 = F + 0xA6C
  hpw : pq.toNat + pl ≤ 0x40000000
  hSp : Sep s 3056 pq pl
  hpub : memBytes M pq pl = pub
  hkt : memBytes M ktq kt.length = kt
  hsc : memBytes M scq sc.length = sc
  mC : memLoad32 M (F + 0xC) = scq
  m10 : memLoad32 M (F + 0x10) = BitVec.ofNat 32 sc.length
  m14 : memLoad32 M (F + 0x14) = BitVec.ofNat 32 kt.length
  hktl : kt.length < 2 ^ 32
  hscl : sc.length < 2 ^ 32
  K : RkK Q s F gL Md (rkKey kt sc pub)

/-- Proves `∀ x, x ∉ rkDc → g x = gL x` through `upd`s of registers in
`rkDc`, `clob`s, and `upd`s of `s8` with `gL 24`. -/
syntax "rkkeep" term : tactic

macro_rules
  | `(tactic| rkkeep $hz) =>
    `(tactic| ((repeat (first | refine keepUpd0 $hz (by decide) ?_ | refine keepClob (by decide) ?_ |
      refine rk_keepS (by rfl) $hz ?_)); try first | assumption | exact fun _ _ => rfl))

section
variable {M0 M1 Md M : Word → BitVec 8} {s out F P : Word} {N : Nat} {g0 gL g : Fin 32 → Word} {Q : Post}
  {kt sc pub : Bytes} {ktq scq pq : Word} {pl : Nat}

theorem RkT.Kn (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl) (h : rkKey kt sc pub = none) :
    RkK Q s F gL Md none := h ▸ T.K

theorem RkT.gsp (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) : g sp = F := (hk 2 (by decide)).trans T.hLsp

theorem RkT.s8 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl) :
    aluEval .add (aluEval .add F 0x7FF) 0x26D = gL 24 := by rw [rk_a6c, T.hL24]

theorem RkT.j628 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (ha0 : (g a0).extractLsb' 0 8 = 0xFF) (h : rkKey kt sc pub = none) :
    WP tufRoleKeysReadCode TRK Q M 0x628 g :=
  rk_628 (key := none) T.hL0 T.hLsp T.hL24 hk T.hW ha0 trivial (T.Kn h)

theorem RkT.j630 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (ha0 : (g a0).extractLsb' 0 8 = 0xFF) (h : rkKey kt sc pub = none) :
    WP tufRoleKeysReadCode TRK Q M 0x630 g :=
  rk_630 (key := none) T.hL0 hk T.hW ha0 trivial (T.Kn h)

theorem RkT.j632 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h23 : g 23 = 9) (ha0 : (g a0).extractLsb' 0 8 = 0xFF)
    (h : rkKey kt sc pub = none) : WP tufRoleKeysReadCode TRK Q M 0x632 g :=
  rk_632 (key := none) T.hL0 hk h23 T.hW ha0 trivial (T.Kn h)

/-! ## The key type -/

/-- The P-256 key type's last byte at 0x4E4. -/
theorem RkT.t4e4 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF) (hs : sc = rkP256s)
    (hm : g a1 = 0 ↔ (kt = rkEcdsa ∨ kt = rkP256s)) : WP tufRoleKeysReadCode TRK Q M 0x4E4 g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  refine WP.aluImm rkr_at_4e4 ?_; wn
  refine WP.aluImm rkr_at_4e8 ?_; wn
  refine WP.aluImm rkr_at_4ec ?_; wn
  rw [hsp, T.s8]
  refine WP.branch rkr_at_4ee (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    have hne := rk_bneT eb
    exact T.j632 (by rkkeep hL0) (by rsimp; try rfl) (by rsimp; exact ha0)
      (rkKey_none_256 hs (fun e => hne (hm.mpr (.inl e))) (fun e => hne (hm.mpr (.inr e))))
  · wn
    rsimp at eb
    have he := hm.mp (rk_bneF eb)
    exact rk_p256 T.E T.hOd T.hW hL0 T.hLsp T.hL24 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9)
      (by rsimp; exact h22) T.hpw T.hSp T.hpub (rkKey_256 hs he ▸ T.K)

/-- The P-384 key type's last byte at 0x68E. -/
theorem RkT.t68e (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF) (hs : sc = rkP384s)
    (hm : g a1 = 0 ↔ (kt = rkEcdsa ∨ kt = rkP384s)) : WP tufRoleKeysReadCode TRK Q M 0x68E g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  refine WP.aluImm rkr_at_68e ?_; wn
  refine WP.aluImm rkr_at_692 ?_; wn
  refine WP.aluImm rkr_at_696 ?_; wn
  rw [hsp, T.s8]
  refine WP.branch rkr_at_698 (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    have hne := rk_bneT eb
    exact T.j632 (by rkkeep hL0) (by rsimp; try rfl) (by rsimp; exact ha0)
      (rkKey_none_384 hs (fun e => hne (hm.mpr (.inl e))) (fun e => hne (hm.mpr (.inr e))))
  · wn
    rsimp at eb
    have he := hm.mp (rk_bneF eb)
    exact rk_p384 T.E T.hOd T.hW hL0 T.hLsp T.hL24 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9)
      (by rsimp; exact h22) T.hpw T.hSp T.hpub (rkKey_384 hs he ▸ T.K)

theorem rk_lenNe {n : Nat} {w : Word} (h : BitVec.ofNat 32 n ≠ w) : n ≠ w.toNat := fun e =>
  h (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, e]; exact Nat.mod_eq_of_lt w.isLt))

theorem rk_lenEq {n : Nat} {w : Word} (hn : n < 2 ^ 32) (h : BitVec.ofNat 32 n = w) : n = w.toNat := by
  rw [← h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem rk_cz {b : BitVec 8} {c : Word} {n : Nat} (hn : n < 256) (hc : c + BitVec.ofNat 32 n = 0) :
    aluEval .add (b.zeroExtend 32) c = 0 ↔ b = BitVec.ofNat 8 n := by
  rw [ev_add]; exact rk_byte0 hn hc

/-- `ecdsa` with the P-256 scheme: the type's last byte. -/
theorem RkT.t4dc (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF) (h23 : g 23 = ktq)
    (hs : sc = rkP256s) (hl : kt.length = 5) (hp : RkPre M ktq rkEcdsa 4) :
    WP tufRoleKeysReadCode TRK Q M 0x4DC g := by
  have hkt : memBytes M ktq 5 = kt := by rw [← hl]; exact T.hkt
  have hL0 := T.hL0
  refine WP.lbu rkr_at_4dc ?_; wn
  refine WP.aluImm rkr_at_4e0 ?_; wn
  refine T.t4e4 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22)
    (by rsimp; exact ha0) hs ?_
  rsimp
  rw [h23]
  refine (rk_lastb (n := 5) hkt hp rfl (by decide) rkEcdsa_b (by decide)).trans ?_
  exact ⟨Or.inl, fun h => h.elim id fun e => absurd (e ▸ hl) (by decide)⟩

/-- The P-256 scheme's full type name: its last byte. -/
theorem RkT.t7f2 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF) (h23 : g 23 = ktq)
    (hs : sc = rkP256s) (hl : kt.length = 19) (hp : RkPre M ktq rkP256s 18) :
    WP tufRoleKeysReadCode TRK Q M 0x7F2 g := by
  have hkt : memBytes M ktq 19 = kt := by rw [← hl]; exact T.hkt
  have hL0 := T.hL0
  refine WP.lbu rkr_at_7f2 ?_; wn
  refine WP.aluImm rkr_at_7f6 ?_; wn
  refine WP.jal rkr_at_7fa (by decide) ?_; wn
  refine T.t4e4 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22)
    (by rsimp; exact ha0) hs ?_
  rsimp
  rw [h23]
  refine (rk_lastb (n := 19) hkt hp rfl (by decide) rkP256s_b (by decide)).trans ?_
  exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hl) (by decide)) id⟩

/-- `ecdsa` with the P-384 scheme: the type's last byte. -/
theorem RkT.t686 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF) (h23 : g 23 = ktq)
    (hs : sc = rkP384s) (hl : kt.length = 5) (hp : RkPre M ktq rkEcdsa 4) :
    WP tufRoleKeysReadCode TRK Q M 0x686 g := by
  have hkt : memBytes M ktq 5 = kt := by rw [← hl]; exact T.hkt
  have hL0 := T.hL0
  refine WP.lbu rkr_at_686 ?_; wn
  refine WP.aluImm rkr_at_68a ?_; wn
  refine T.t68e (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22)
    (by rsimp; exact ha0) hs ?_
  rsimp
  rw [h23]
  refine (rk_lastb (n := 5) hkt hp rfl (by decide) rkEcdsa_b (by decide)).trans ?_
  exact ⟨Or.inl, fun h => h.elim id fun e => absurd (e ▸ hl) (by decide)⟩

/-- The P-384 scheme's full type name: its last byte. -/
theorem RkT.t8d4 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF) (h23 : g 23 = ktq)
    (hs : sc = rkP384s) (hl : kt.length = 19) (hp : RkPre M ktq rkP384s 18) :
    WP tufRoleKeysReadCode TRK Q M 0x8D4 g := by
  have hkt : memBytes M ktq 19 = kt := by rw [← hl]; exact T.hkt
  have hL0 := T.hL0
  refine WP.lbu rkr_at_8d4 ?_; wn
  refine WP.aluImm rkr_at_8d8 ?_; wn
  refine WP.jal rkr_at_8dc (by decide) ?_; wn
  refine T.t68e (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22)
    (by rsimp; exact ha0) hs ?_
  rsimp
  rw [h23]
  refine (rk_lastb (n := 19) hkt hp rfl (by decide) rkP384s_b (by decide)).trans ?_
  exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hl) (by decide)) id⟩

/-- The key type's length with the rkP256s scheme. -/
theorem RkT.t49c (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF)
    (h23 : g 23 = ktq) (hs : sc = rkP256s) : WP tufRoleKeysReadCode TRK Q M 0x49C g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  have hal : (F + 0x14).toNat % 4 = 0 := T.E.alF (c := 0x14) (by decide)
  have hg0 : g 0 = 0 := (hk 0 (by decide)).trans hL0
  refine WP.aluImm rkr_at_49c ?_; wn
  rw [hg0]
  refine WP.lw rkr_at_49e (by rsimp; rw [hsp]; exact hal) ?_; wn
  refine WP.branch rkr_at_4a0 (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    have e := rk_beqT eb
    rw [hsp, T.m14] at e
    have hl : kt.length = 19 := rk_lenEq T.hktl e
    exact rk_chain (rl := false) (r := 23) (tg := 0x628) (L := rkP256s) (q := ktq) (F := F) (by decide) (by decide)
      rkP256s_b 18 0x71C 0 0x7F2 _ rk_ch_71c (fun h => absurd h (by decide)) (fun _ => by rsimp; exact h23)
      RkPre.nil
      (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
        (rkKey_none_256 hs (rk_lne T.hkt (by rw [hl]; decide)) (rk_ne T.hkt (by omega) hne)))
      (fun v hp => T.t7f2 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22)
        (by rsimp; exact ha0) (by rsimp; exact h23) hs hl hp)
  · wn
    rsimp at eb
    have e := rk_beqF eb
    rw [hsp, T.m14] at e
    have n19 : kt.length ≠ 19 := rk_lenNe e
    refine WP.aluImm rkr_at_4a4 ?_; wn
    refine WP.lw rkr_at_4a6 (by rsimp; rw [hsp]; exact hal) ?_; wn
    refine WP.branch rkr_at_4a8 (fun eb => ?_) (fun eb => ?_)
    · wn
      rsimp at eb
      have e := rk_bneT eb
      rw [hsp, T.m14] at e
      have n5 : kt.length ≠ 5 := rk_lenNe e
      exact T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
        (rkKey_none_256 hs (rk_lne T.hkt n5) (rk_lne T.hkt n19))
    · wn
      rsimp at eb
      have e := rk_bneF eb
      rw [hsp, T.m14] at e
      have hl : kt.length = 5 := rk_lenEq T.hktl e
      exact rk_chain (rl := false) (r := 23) (tg := 0x628) (L := rkEcdsa) (q := ktq) (F := F) (by decide)
        (by decide) rkEcdsa_b 4 0x4AC 0 0x4DC _ rk_ch_4ac (fun h => absurd h (by decide))
        (fun _ => by rsimp; exact h23) RkPre.nil
        (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
          (rkKey_none_256 hs (rk_ne T.hkt (by omega) hne) (rk_lne T.hkt (by rw [hl]; decide))))
        (fun v hp => T.t4dc (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22)
          (by rsimp; exact ha0) (by rsimp; exact h23) hs hl hp)

/-- The key type's length with the rkP384s scheme. -/
theorem RkT.t64e (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF)
    (h23 : g 23 = ktq) (hs : sc = rkP384s) : WP tufRoleKeysReadCode TRK Q M 0x64E g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  have hal : (F + 0x14).toNat % 4 = 0 := T.E.alF (c := 0x14) (by decide)
  have hg0 : g 0 = 0 := (hk 0 (by decide)).trans hL0
  refine WP.aluImm rkr_at_64e ?_; wn
  rw [hg0]
  refine WP.lw rkr_at_650 (by rsimp; rw [hsp]; exact hal) ?_; wn
  refine WP.branch rkr_at_652 (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    have e := rk_beqT eb
    rw [hsp, T.m14] at e
    have hl : kt.length = 19 := rk_lenEq T.hktl e
    exact rk_chain (rl := false) (r := 23) (tg := 0x628) (L := rkP384s) (q := ktq) (F := F) (by decide) (by decide)
      rkP384s_b 18 0x7FC 0 0x8D4 _ rk_ch_7fc (fun h => absurd h (by decide)) (fun _ => by rsimp; exact h23)
      RkPre.nil
      (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
        (rkKey_none_384 hs (rk_lne T.hkt (by rw [hl]; decide)) (rk_ne T.hkt (by omega) hne)))
      (fun v hp => T.t8d4 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22)
        (by rsimp; exact ha0) (by rsimp; exact h23) hs hl hp)
  · wn
    rsimp at eb
    have e := rk_beqF eb
    rw [hsp, T.m14] at e
    have n19 : kt.length ≠ 19 := rk_lenNe e
    refine WP.aluImm rkr_at_656 ?_; wn
    refine WP.lw rkr_at_658 (by rsimp; rw [hsp]; exact hal) ?_; wn
    refine WP.branch rkr_at_65a (fun eb => ?_) (fun eb => ?_)
    · wn
      rsimp at eb
      have e := rk_bneT eb
      rw [hsp, T.m14] at e
      have n5 : kt.length ≠ 5 := rk_lenNe e
      exact T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
        (rkKey_none_384 hs (rk_lne T.hkt n5) (rk_lne T.hkt n19))
    · wn
      rsimp at eb
      have e := rk_bneF eb
      rw [hsp, T.m14] at e
      have hl : kt.length = 5 := rk_lenEq T.hktl e
      exact rk_chain (rl := false) (r := 23) (tg := 0x628) (L := rkEcdsa) (q := ktq) (F := F) (by decide)
        (by decide) rkEcdsa_b 4 0x65E 0 0x686 _ rk_ch_65e (fun h => absurd h (by decide))
        (fun _ => by rsimp; exact h23) RkPre.nil
        (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
          (rkKey_none_384 hs (rk_ne T.hkt (by omega) hne) (rk_lne T.hkt (by rw [hl]; decide))))
        (fun v hp => T.t686 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22)
          (by rsimp; exact ha0) (by rsimp; exact h23) hs hl hp)

/-- The P-256 scheme's last two bytes. -/
theorem RkT.t480 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF)
    (h23 : g 23 = ktq) (hsl : sc.length = 19) (hp : RkPre M scq rkP256s 17) :
    WP tufRoleKeysReadCode TRK Q M 0x480 g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  have h16 : M (scq + BitVec.ofNat 32 16) ≠ BitVec.ofNat 8 (rkP384s.getD 16 0) := by
    rw [hp 16 (by decide)]; decide
  exact rk_chain (rl := true) (r := 12) (tg := 0x628) (L := rkP256s) (q := scq) (F := F) (by decide) (by decide)
    rkP256s_b 2 0x480 17 0x49C g rk_ch_480 (fun _ => ⟨hsp, T.mC, T.E.alF (c := 0xC) (by decide)⟩)
    (fun h => absurd h (by decide)) hp
    (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
      (rkKey_none_of (rk_ne T.hsc (by omega) hne) (rk_ne T.hsc (by omega) h16)
        (.inr (rk_lne T.hsc (by rw [hsl]; decide)))))
    (fun v hp' => T.t49c (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; exact ha0) (by rsimp; exact h23)
      (by rw [← T.hsc, hsl]; exact hp'.eq rfl rkP256s_b))

/-- The P-384 scheme's last two bytes. -/
theorem RkT.t636 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF)
    (h23 : g 23 = ktq) (hsl : sc.length = 19) (hp : RkPre M scq rkP384s 17) :
    WP tufRoleKeysReadCode TRK Q M 0x636 g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  have h16 : M (scq + BitVec.ofNat 32 16) ≠ BitVec.ofNat 8 (rkP256s.getD 16 0) := by
    rw [hp 16 (by decide)]; decide
  exact rk_chain (rl := true) (r := 12) (tg := 0x628) (L := rkP384s) (q := scq) (F := F) (by decide) (by decide)
    rkP384s_b 2 0x636 17 0x64E g rk_ch_636 (fun _ => ⟨hsp, T.mC, T.E.alF (c := 0xC) (by decide)⟩)
    (fun h => absurd h (by decide)) hp
    (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
      (rkKey_none_of (rk_ne T.hsc (by omega) h16) (rk_ne T.hsc (by omega) hne)
        (.inr (rk_lne T.hsc (by rw [hsl]; decide)))))
    (fun v hp' => T.t64e (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; exact ha0) (by rsimp; exact h23)
      (by rw [← T.hsc, hsl]; exact hp'.eq rfl rkP384s_b))

/-- The scheme's byte 16 picks P-256 or P-384. -/
theorem RkT.t46a (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF)
    (h23 : g 23 = ktq) (hsl : sc.length = 19) (hp : RkPre M scq rkP256s 16) :
    WP tufRoleKeysReadCode TRK Q M 0x46A g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  refine WP.lw rkr_at_46a (by (try rsimp); rw [hsp]; exact T.E.alF (c := 0xC) (by decide)) ?_; wn
  rw [hsp, T.mC]
  refine WP.lbu rkr_at_46c ?_; wn
  refine WP.aluImm rkr_at_470 ?_; wn
  refine WP.branch rkr_at_474 (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    have hb := (rk_cz (n := 0x33) (by decide) (by decide)).mp (rk_beqT eb)
    exact T.t636 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; exact ha0) (by rsimp; exact h23) hsl
      ((hp.cast rk_p384_pfx).snoc hb)
  · wn
    rsimp at eb
    have hb3 : M (scq + 0x10) ≠ BitVec.ofNat 8 0x33 := fun e =>
      rk_beqF eb ((rk_cz (by decide) (by decide)).mpr e)
    refine WP.aluImm rkr_at_478 ?_; wn
    refine WP.branch rkr_at_47c (fun eb => ?_) (fun eb => ?_)
    · wn
      rsimp at eb
      have hb2 : M (scq + 0x10) ≠ BitVec.ofNat 8 0x32 := fun e =>
        rk_bneT eb ((rk_cz (by decide) (by decide)).mpr e)
      exact T.j628 (by rkkeep hL0) (by rsimp; exact ha0)
        (rkKey_none_of (rk_ne T.hsc (j := 16) (by omega) hb2) (rk_ne T.hsc (j := 16) (by omega) hb3)
          (.inr (rk_lne T.hsc (by rw [hsl]; decide))))
    · wn
      rsimp at eb
      have hb := (rk_cz (n := 0x32) (by decide) (by decide)).mp (rk_bneF eb)
      exact T.t480 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; exact ha0) (by rsimp; exact h23) hsl (hp.snoc hb)

/-- A 19-byte scheme: bytes 0 to 15 are the shared `ecdsa-sha2-nistp` prefix. -/
theorem RkT.t384 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF)
    (h23 : g 23 = ktq) (hsl : sc.length = 19) : WP tufRoleKeysReadCode TRK Q M 0x384 g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  have hnone : ∀ {j}, j < 16 → M (scq + BitVec.ofNat 32 j) ≠ BitVec.ofNat 8 (rkP256s.getD j 0) →
      rkKey kt sc pub = none := fun hj hne =>
    rkKey_none_of (rk_ne T.hsc (by omega) hne) (rk_ne T.hsc (by omega) (rk_p384_pfx _ hj ▸ hne))
      (.inr (rk_lne T.hsc (by rw [hsl]; decide)))
  refine WP.lw rkr_at_384 (by (try rsimp); rw [hsp]; exact T.E.alF (c := 0xC) (by decide)) ?_; wn
  rw [hsp, T.mC]
  refine WP.lbu rkr_at_386 ?_; wn
  refine WP.aluImm rkr_at_38a ?_; wn
  refine WP.aluImm rkr_at_38e ?_; wn
  refine WP.branch rkr_at_392 (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    exact T.j628 (by rkkeep hL0) (by rsimp; try rfl)
      (hnone (j := 0) (by decide) fun e => rk_bneT eb ((rk_cz (by decide) (by decide)).mpr e))
  · wn
    rsimp at eb
    have hb0 := (rk_cz (n := 0x65) (by decide) (by decide)).mp (rk_bneF eb)
    refine WP.lbu rkr_at_396 ?_; wn
    refine WP.aluImm rkr_at_39a ?_; wn
    refine WP.aluImm rkr_at_39e ?_; wn
    refine WP.aluImm rkr_at_3a2 ?_; wn
    rw [hsp, T.s8]
    refine WP.branch rkr_at_3a6 (fun eb => ?_) (fun eb => ?_)
    · wn
      rsimp at eb
      exact T.j630 (by rkkeep hL0) (by rsimp; try rfl)
        (hnone (j := 1) (by decide) fun e => rk_bneT eb ((rk_cz (by decide) (by decide)).mpr e))
    · wn
      rsimp at eb
      have hb1 := (rk_cz (n := 0x63) (by decide) (by decide)).mp (rk_bneF eb)
      have hp2 : RkPre M scq rkP256s 2 := (RkPre.nil.snoc hb0).snoc hb1
      refine rk_chain (rl := false) (r := 12) (tg := 0x630) (L := rkP256s) (q := scq) (F := F) (by decide)
        (by decide) rkP256s_b 1 0x3AA 2 0x3B6 _ rk_ch_3aa (fun h => absurd h (by decide)) (fun _ => by rsimp) hp2
        (fun j v hj _ hne => T.j630 (by rkkeep hL0) (by rsimp; try rfl) (hnone (by omega) hne)) (fun v hp3 => ?_)
      refine rk_chain (rl := false) (r := 12) (tg := 0x628) (L := rkP256s) (q := scq) (F := F) (by decide)
        (by decide) rkP256s_b 1 0x3B6 3 0x3C2 _ rk_ch_3b6 (fun h => absurd h (by decide)) (fun _ => by rsimp) hp3
        (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; try rfl) (hnone (by omega) hne)) (fun v hp4 => ?_)
      refine rk_chain (rl := true) (r := 12) (tg := 0x628) (L := rkP256s) (q := scq) (F := F) (by decide)
        (by decide) rkP256s_b 12 0x3C2 4 0x46A _ rk_ch_3c2
        (fun _ => ⟨by rsimp; exact hsp, T.mC, T.E.alF (c := 0xC) (by decide)⟩) (fun h => absurd h (by decide)) hp4
        (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; try rfl) (hnone (by omega) hne)) (fun v hp16 => ?_)
      exact T.t46a (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; try rfl) (by rsimp; exact h23) hsl hp16

/-- `ed25519`: the scheme's last byte. -/
theorem RkT.t5e6 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (ha0 : (g a0).extractLsb' 0 8 = 0xFF)
    (hke : kt = rkEd) (hsl7 : sc.length = 7) (hps : RkPre M scq rkEd 6) :
    WP tufRoleKeysReadCode TRK Q M 0x5E6 g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  have hsc : memBytes M scq 7 = sc := by rw [← hsl7]; exact T.hsc
  have hn256 : sc ≠ rkP256s := rk_lne T.hsc (by rw [hsl7]; decide)
  have hn384 : sc ≠ rkP384s := rk_lne T.hsc (by rw [hsl7]; decide)
  refine WP.lw rkr_at_5e6 (by (try rsimp); rw [hsp]; exact T.E.alF (c := 0xC) (by decide)) ?_; wn
  refine WP.lbu rkr_at_5e8 ?_; wn
  refine WP.aluImm rkr_at_5ec ?_; wn
  refine WP.aluImm rkr_at_5f0 ?_; wn
  refine WP.aluImm rkr_at_5f4 ?_; wn
  refine WP.aluImm rkr_at_5f8 ?_; wn
  rw [hsp, T.s8, T.mC]
  have hm := rk_lastb (n := 7) (c := 0xFFFFFFC7) hsc hps rfl (by decide) rkEd_b (by decide)
  refine WP.branch rkr_at_5fa (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    have hne := rk_bneT eb
    exact T.j632 (by rkkeep hL0) (by rsimp; try rfl) (by rsimp; exact ha0)
      (rkKey_none_of hn256 hn384 (.inr fun e => hne (hm.mpr e)))
  · wn
    rsimp at eb
    exact rk_ed T.E T.hOd T.hW hL0 T.hLsp T.hL24 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9)
      (by rsimp; exact h22) T.hpw T.hSp T.hpub (rkKey_ed hke (hm.mp (rk_bneF eb)) ▸ T.K)

/-- A scheme that isn't 19 bytes: only `ed25519` with `ed25519` is a key. -/
theorem RkT.t548 (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF)
    (h23 : g 23 = ktq) (hsl : sc.length ≠ 19) (h13 : g a3 = BitVec.ofNat 32 sc.length) :
    WP tufRoleKeysReadCode TRK Q M 0x548 g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  have hn256 : sc ≠ rkP256s := rk_lne T.hsc hsl
  have hn384 : sc ≠ rkP384s := rk_lne T.hsc hsl
  have hg0 : g 0 = 0 := (hk 0 (by decide)).trans hL0
  refine WP.aluImm rkr_at_548 ?_; wn
  rw [hg0]
  refine WP.aluImm rkr_at_54c ?_; wn
  refine WP.lw rkr_at_54e (by (try rsimp); rw [hsp]; exact T.E.alF (c := 0x14) (by decide)) ?_; wn
  refine WP.branch rkr_at_550 (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    have e := rk_bneT eb
    rw [hsp, T.m14] at e
    exact T.j628 (by rkkeep hL0) (by rsimp; try rfl) (rkKey_none_of hn256 hn384 (.inl (rk_lne T.hkt (rk_lenNe e))))
  · wn
    rsimp at eb
    have e := rk_bneF eb
    rw [hsp, T.m14] at e
    have hl : kt.length = 7 := rk_lenEq T.hktl e
    refine WP.branch rkr_at_554 (fun eb => ?_) (fun eb => ?_)
    · wn
      rsimp at eb
      have e := rk_bneT eb
      rw [h13] at e
      exact T.j628 (by rkkeep hL0) (by rsimp; try rfl)
        (rkKey_none_of hn256 hn384 (.inr (rk_lne T.hsc (rk_lenNe e))))
    · wn
      rsimp at eb
      have e := rk_bneF eb
      rw [h13] at e
      have hsl7 : sc.length = 7 := rk_lenEq T.hscl e
      refine rk_chain (rl := false) (r := 23) (tg := 0x628) (L := rkEd) (q := ktq) (F := F) (by decide)
        (by decide) rkEd_b 7 0x558 0 0x59E _ rk_ch_558 (fun h => absurd h (by decide))
        (fun _ => by rsimp; exact h23) RkPre.nil
        (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; try rfl)
          (rkKey_none_of hn256 hn384 (.inl (rk_ne T.hkt (by omega) hne)))) (fun v hpk => ?_)
      have hke : kt = rkEd := by rw [← T.hkt, hl]; exact hpk.eq rfl rkEd_b
      refine rk_chain (rl := true) (r := 12) (tg := 0x628) (L := rkEd) (q := scq) (F := F) (by decide)
        (by decide) rkEd_b 6 0x59E 0 0x5E6 _ rk_ch_59e
        (fun _ => ⟨by rsimp; exact hsp, T.mC, T.E.alF (c := 0xC) (by decide)⟩) (fun h => absurd h (by decide))
        RkPre.nil
        (fun j v hj _ hne => T.j628 (by rkkeep hL0) (by rsimp; try rfl)
          (rkKey_none_of hn256 hn384 (.inr (rk_ne T.hsc (by omega) hne)))) (fun v hps => ?_)
      exact T.t5e6 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; try rfl) hke hsl7 hps

/-- The tree from 0x37C: dispatch on the scheme's length. -/
theorem RkT.t37c (T : RkT M0 M1 Md M s out F P N g0 gL Q kt sc pub ktq scq pq pl)
    (hk : ∀ x, x ∉ rkDc → g x = gL x) (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF)
    (h23 : g 23 = ktq) : WP tufRoleKeysReadCode TRK Q M 0x37C g := by
  have hsp := T.gsp hk
  have hL0 := T.hL0
  have hg0 : g 0 = 0 := (hk 0 (by decide)).trans hL0
  refine WP.aluImm rkr_at_37c ?_; wn
  rw [hg0]
  refine WP.lw rkr_at_37e (by (try rsimp); rw [hsp]; exact T.E.alF (c := 0x10) (by decide)) ?_; wn
  rw [hsp, T.m10]
  refine WP.branch rkr_at_380 (fun eb => ?_) (fun eb => ?_)
  · wn
    rsimp at eb
    exact T.t548 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; exact h23) (rk_lenNe (rk_bneT eb)) (by rsimp)
  · wn
    rsimp at eb
    exact T.t384 (by rkkeep hL0) (by rsimp; exact h8) (by rsimp; exact h9) (by rsimp; exact h22) (by rsimp; exact h23) (rk_lenEq T.hscl (rk_bneF eb))

end

end C3.RV32
