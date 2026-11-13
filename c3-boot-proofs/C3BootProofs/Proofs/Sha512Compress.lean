import C3BootProofs.Proofs.Sha512Frame

/-!
# `sha2::sha512::compress512`, end to end

The outer loop at 0x82 runs once per 128-byte block: it loads the block's
big-endian words into the buffer at `F + 0x58`, copies them into the
schedule array at `F + 0xD8`, clears the rest of the array, computes the
schedule, runs the 80 rounds, and adds the working variables into the state
at `stp`. `s5Compress_correct` composes it with the prologue and the
epilogue.
-/

namespace C3.RV32

open C3.Image

/-- The 64-bit word whose halves are `l` and `h`. -/
def pk (l h : Word) : Sha512.W64 := BitVec.ofNat 64 (l.toNat + 2 ^ 32 * h.toNat)

theorem lo64_pk (l h : Word) : lo64 (pk l h) = l := by
  apply BitVec.eq_of_toNat_eq
  rw [lo64_toNat, pk, BitVec.toNat_ofNat]
  have := l.isLt; have := h.isLt
  omega

theorem hi64_pk (l h : Word) : hi64 (pk l h) = h := by
  apply BitVec.eq_of_toNat_eq
  rw [hi64_toNat, pk, BitVec.toNat_ofNat]
  have := l.isLt; have := h.isLt
  omega

theorem pk_lohi (X : Sha512.W64) : pk (lo64 X) (hi64 X) = X := by
  apply BitVec.eq_of_toNat_eq
  rw [pk, BitVec.toNat_ofNat, ← val64]
  exact Nat.mod_eq_of_lt X.isLt

/-- The state's eight words at `stp`, each low half first. -/
def s5Hv (M : Word → BitVec 8) (stp : Word) : Sha512.V8 :=
  ⟨pk (memLoad32 M (stp + 0x0)) (memLoad32 M (stp + 0x4)), pk (memLoad32 M (stp + 0x8)) (memLoad32 M (stp + 0xC)),
   pk (memLoad32 M (stp + 0x10)) (memLoad32 M (stp + 0x14)), pk (memLoad32 M (stp + 0x18)) (memLoad32 M (stp + 0x1C)),
   pk (memLoad32 M (stp + 0x20)) (memLoad32 M (stp + 0x24)), pk (memLoad32 M (stp + 0x28)) (memLoad32 M (stp + 0x2C)),
   pk (memLoad32 M (stp + 0x30)) (memLoad32 M (stp + 0x34)), pk (memLoad32 M (stp + 0x38)) (memLoad32 M (stp + 0x3C))⟩

/-- The state plus the working variables, section 6.4.2 step 4. -/
def s5Add (hv v : Sha512.V8) : Sha512.V8 :=
  ⟨hv.a + v.a, hv.b + v.b, hv.c + v.c, hv.d + v.d, hv.e + v.e, hv.f + v.f, hv.g + v.g, hv.h + v.h⟩

theorem s5Add_toList (hv v : Sha512.V8) :
    (s5Add hv v).toList = List.zipWith (· + ·) hv.toList v.toList := rfl

/-- A 64-bit addition as the feed-forward computes it. -/
theorem add64_pair {X Y : Sha512.W64} {l c h : Word} (hl : l = lo64 X + lo64 Y)
    (hc : c = aluEval .sltu l (lo64 Y)) (hh : h = hi64 Y + hi64 X + c) : l = lo64 (X + Y) ∧ h = hi64 (X + Y) := by
  have P := holdsN_add (holdsN_atom X) (holdsN_atom Y) (l := l) (c := c)
    (by rw [hl]; exact BitVec.toNat_add _ _) (by rw [hc, hl]; exact sltu_carry' _ _)
  exact holdsN_halves P (dm_add (x := h) (y := hi64 Y + hi64 X) (z := c) (by rw [hh]; exact BitVec.toNat_add _ _)
    (dm_add (BitVec.toNat_add _ _) (dm_leaf _) (dm_leaf _)) (dm_leaf c)) (by ac_rfl)

/-- The registers `compress512` never writes. -/
def s5Keep (q : Fin 32) : Bool := q.val == 3 || q.val == 4

/-- What the function needs and doesn't change: its code and its callees'
at their offsets from an even `P`, the round constants, the aligned state at
`stp`, the `n` blocks at `bp`, and the frame `F`, all apart where they
must be. -/
structure S5OS (P F stp bp : Word) (n : Nat) (M0 : Word → BitVec 8) : Prop where
  hP : P.toNat % 2 = 0
  hF : F.toNat % 4 = 0
  hFw : F.toNat + 0x390 ≤ 2 ^ 32
  hstp : stp.toNat % 4 = 0
  hwbp : bp.toNat + 128 * n < 2 ^ 32
  code : CodeIn M0 P sha512CompressCode
  idx : CodeIn M0 (P + 0xFFFFFFEA) rangeFromIndexCode
  stub : CodeIn M0 (P + 0x5AC) memcpyStubCode
  body : CodeIn M0 (P + 0x5B4) memcpyBodyCode
  mset : CodeIn M0 (P + 0x544) memsetCode
  kd : CodeIn M0 s5K sha512KData
  sC : Sep F 0x390 P sha512CompressCode.length
  sI : Sep F 0x390 (P + 0xFFFFFFEA) rangeFromIndexCode.length
  sU : Sep F 0x390 (P + 0x5AC) memcpyStubCode.length
  sB : Sep F 0x390 (P + 0x5B4) memcpyBodyCode.length
  sZ : Sep F 0x390 (P + 0x544) memsetCode.length
  sK : Sep F 0x390 s5K 640
  stC : Sep stp 128 P sha512CompressCode.length
  stI : Sep stp 128 (P + 0xFFFFFFEA) rangeFromIndexCode.length
  stU : Sep stp 128 (P + 0x5AC) memcpyStubCode.length
  stB : Sep stp 128 (P + 0x5B4) memcpyBodyCode.length
  stZ : Sep stp 128 (P + 0x544) memsetCode.length
  stK : Sep stp 128 s5K 640
  stF : Sep stp 128 F 0x390
  bF : Sep bp (128 * n) F 0x390
  bSt : Sep bp (128 * n) stp 128

theorem S5OS.cIn {P F stp bp : Word} {n : Nat} {M0 M : Word → BitVec 8} (_ : S5OS P F stp bp n M0)
    (fr : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → M x = M0 x) {b : Word} {code : List Nat} {k : Nat}
    (hc : CodeIn M0 b code) (h1 : Sep F 0x390 b k) (h2 : Sep stp 128 b k) (hk : code.length ≤ k) :
    CodeIn M b code := fun i hi => by
  rw [fr _ (h1.subR (c := i) (l := 1) (by omega)) (h2.subR (c := i) (l := 1) (by omega))]; exact hc i hi

set_option maxRecDepth 100000 in
theorem sha512KData_len : sha512KData.length = 640 := rfl

/-- What holds at 0x82 before block `j`, with the state `hv` after `j`
blocks: `Ms` holds the registers the prologue saved, and `g` is the
register file at entry. -/
structure S5O (P F stp bp : Word) (n : Nat) (M0 Ms : Word → BitVec 8) (g : Fin 32 → Word) (j : Nat)
    (hv : Sha512.V8) (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0x82 (reg m)
  rsp : reg m sp = F
  r21 : reg m 21 = bp + BitVec.ofNat 32 (128 * j)
  al : reg m 23 = lo64 hv.a
  ah : reg m 19 = hi64 hv.a
  bl : reg m 22 = lo64 hv.b
  bh : reg m 27 = hi64 hv.b
  cl : reg m 24 = lo64 hv.c
  ch : reg m 26 = hi64 hv.c
  dl : reg m 18 = lo64 hv.d
  dh : memLoad32 M (F + 0x54) = hi64 hv.d
  el : reg m 20 = lo64 hv.e
  eh : memLoad32 M (F + 0x4C) = hi64 hv.e
  fl : memLoad32 M (F + 0x50) = lo64 hv.f
  fh : memLoad32 M (F + 0x44) = hi64 hv.f
  gl : memLoad32 M (F + 0x48) = lo64 hv.g
  gh : memLoad32 M (F + 0x3C) = hi64 hv.g
  hl : memLoad32 M (F + 0x40) = lo64 hv.h
  hh : memLoad32 M (F + 0x38) = hi64 hv.h
  mst : memLoad32 M (F + 0xC) = stp
  mend : memLoad32 M (F + 0x10) = bp + BitVec.ofNat 32 (128 * n)
  hst : s5Hv M stp = hv
  sv : ∀ x, Sep F 0x35C x 1 → Sep stp 128 x 1 → M x = Ms x
  fr : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → M x = M0 x
  keep : ∀ q, s5Keep q = true → reg m q = g q

theorem beq_blocks128 {bp : Word} {j n : Nat} (hj : j < n) (hw : bp.toNat + 128 * n < 2 ^ 32) :
    branchTaken .beq (bp + BitVec.ofNat 32 (128 * j)) (bp + BitVec.ofNat 32 (128 * n)) = false := by
  unfold branchTaken
  rw [beq_eq_false_iff_ne]
  exact add_ofNat_ne bp (by omega) (by omega) (by omega)

theorem frame_toNat5 {F : Word} (hFw : F.toNat + 0x390 ≤ 2 ^ 32) {c : Nat} (hc : c < 0x390) :
    (F + BitVec.ofNat 32 c).toNat = F.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

theorem s5W_rec (M0 : Word → BitVec 8) (cur : Word) : S5Rec (s5W M0 cur) :=
  fun _ h1 h2 => Sha512.sched_rec _ h1 h2

/-- A frame slot below the buffer, after the buffer, the array, and the
`memset` writes, which all lie at or above `F + 0x58`. -/
theorem low_load {F : Word} {M M' : Word → BitVec 8} (hFw : F.toNat + 0x390 ≤ 2 ^ 32)
    (h : ∀ x, Sep (F + BitVec.ofNat 32 0x58) 0x300 x 1 → M' x = M x) {c : Nat} (hc : c + 4 ≤ 0x58) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) :=
  load_congr h (frame_sep (.inr (by omega)) (by omega) (by omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- One block, from 0x82 back to 0x82. -/
theorem s5_block {P F stp bp : Word} {n j : Nat} {M0 Ms M : Word → BitVec 8} {g : Fin 32 → Word}
    {hv : Sha512.V8} {m : Machine} {cur : Word} (S : S5OS P F stp bp n M0)
    (O : S5O P F stp bp n M0 Ms g j hv M m) (hj : j < n) (hcur : cur = bp + BitVec.ofNat 32 (128 * j)) :
    ∃ m' M', Steps m m' ∧
      S5O P F stp bp n M0 Ms g (j + 1) (s5Add hv (Sha512.vs (s5W M0 cur) hv 80)) M' m' := by
  have hFw := S.hFw
  have hc0 := S.cIn O.fr S.code S.sC S.stC (Nat.le_refl _)
  have hi0 := S.cIn O.fr S.idx S.sI S.stI (Nat.le_refl _)
  -- 0x82: the buffer's address, the end of the blocks, and the exit test
  obtain ⟨m1, c1, u1⟩ := St.block s5Top O.st hc0 s5Top_end
    (by simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Top, upd_app, ↓reduceIte, and_true, true_and]
        rw [O.rsp]; exact fr_al S.hF (by decide))
  simp only [runBlock, BInstr.run, s5Top] at u1
  have x25 : reg m1 25 = F + 0x58 := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [O.rsp]; rfl
  have k1 : ∀ q, q.val ≠ 0 → q ≠ 25 → q ≠ a0 → reg m1 q = reg m q := fun q h0 h1 h2 => by
    rw [u1.regs]; simp only [upd_app, h0, h1, h2, ite_false]
  obtain ⟨m2, d2, u2⟩ := u1.self.notTaken hc0 0x8C s5_at_88 (by decide) (by
    rw [k1 21 (by decide) (by decide) (by decide), O.r21, u1.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [O.rsp, O.mend]; exact beq_blocks128 hj S.hwbp)
  -- 0x8C: the next block's address at `F + 0x34`
  have sF34 : Sep (F + 0x34) 4 P sha512CompressCode.length := frm_sep S.sC (by decide)
  obtain ⟨m3, c3, u3⟩ := St.block s5Blk u2 hc0 s5Blk_end
    (by simp +decide only [BlockOk, BInstr.ok, BInstr.run, s5Blk, upd_app, ↓reduceIte, and_true, true_and]
        rw [k1 sp (by decide) (by decide) (by decide), O.rsp]; exact ⟨fr_al S.hF (by decide), sF34⟩)
  simp only [runBlock, BInstr.run, s5Blk] at u3
  simp +decide only [upd_app, ↓reduceIte] at u3
  rw [k1 sp (by decide) (by decide) (by decide), O.rsp, k1 21 (by decide) (by decide) (by decide), O.r21,
    ← hcur] at u3
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 M (F + 0x34) (aluEval .add cur 0x80) = M1 := ⟨_, rfl⟩
  rw [hM1] at u3
  have frM1 : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → M1 x = M0 x := fun x h1 h2 => by
    rw [← hM1, st_get_sep h1 (by decide), O.fr x h1 h2]
  have k3 : ∀ q, q.val ≠ 0 → q ≠ 25 → q ≠ a0 → q ≠ 8 → reg m3 q = reg m q := fun q h0 h1 h2 h3 => by
    rw [u3.regs]; simp only [upd_app, h0, h1, h2, h3, ite_false]; exact k1 q h0 h1 h2
  -- the load loop
  have sBuf : Sep (F + BitVec.ofNat 32 0x58) 0x80 cur 128 := by
    rw [hcur]; exact (S.bF.symm.sub (c := 0x58) (l := 0x80) (by decide)).subR (c := 128 * j) (l := 128) (by omega)
  have blk : ∀ i, i < 128 → M1 (cur + BitVec.ofNat 32 i) = M0 (cur + BitVec.ofNat 32 i) := fun i hi => by
    rw [hcur, add_ofNat_assoc]
    exact frM1 _ (S.bF.symm.subR (c := 128 * j + i) (l := 1) (by omega))
      (S.bSt.symm.subR (c := 128 * j + i) (l := 1) (by omega))
  have LS : S5LS P F cur M0 M1 :=
    ⟨S.hP, S.hF, hFw, S.sC.sub (by decide), S.sI.sub (by decide), sBuf, blk⟩
  have L0 : S5L P F cur M0 M1 (reg m3) 0 M1 m3 := by
    refine ⟨u3.self, S.cIn frM1 S.code S.sC S.stC (Nat.le_refl _), S.cIn frM1 S.idx S.sI S.stI (Nat.le_refl _),
      ?_, ?_, ?_, fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ => rfl⟩
    · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rfl
    · rw [k3 21 (by decide) (by decide) (by decide) (by decide), O.r21, hcur]
    · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [x25]; rfl
  obtain ⟨m4, Ml, c4, L16⟩ := s5_load_from LS 16 0 M1 m3 rfl L0
  obtain ⟨m5, c5, u5, k5⟩ := s5_load_exit L16
  have frMl : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → Ml x = M0 x := fun x h1 h2 => by
    rw [L16.fr x (h1.sub (c := 0x58) (l := 0x80) (by decide)), frM1 x h1 h2]
  have E5 : ∀ q, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 26, 27] → reg m5 q = reg m q := fun q hq => by
    have h1 : s5LdKeep q = true := by revert q; decide
    have hq' : q.val ≠ 0 ∧ q ≠ 25 ∧ q ≠ a0 ∧ q ≠ 8 := by revert q; decide
    rw [k5 q h1, k3 q hq'.1 hq'.2.1 hq'.2.2.1 hq'.2.2.2]
  have sp5 : reg m5 sp = F := (E5 sp (by decide)).trans O.rsp
  -- 0xF8: `memcpy` of the buffer into the array's first 128 bytes
  obtain ⟨m6, c6, u6⟩ := St.block s5Cpy u5 L16.code s5Cpy_end (by simp [BlockOk, BInstr.ok, s5Cpy])
  simp only [runBlock, BInstr.run, s5Cpy] at u6
  have e8 : P + 0x5AC + 8 = P + 0x5B4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m7, c7, u7, a07, k7⟩ := St.memcpyW (B := P + 0x5AC) (w := 32)
    (dst := F + BitVec.ofNat 32 0xD8) (src := F + BitVec.ofNat 32 0x58)
    (even_at P S.hP 0x5AC (by decide)) u6 L16.code (S.cIn frMl S.stub S.sU S.stU (Nat.le_refl _))
    (by rw [e8]; exact S.cIn frMl S.body S.sB S.stB (Nat.le_refl _))
    s5_at_100 s5_at_104 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P S.hP (0x100 + 8) (by decide))
    (by decide) (by rw [frame_toNat5 hFw (by decide)]; omega) (by decide)
    (aligned_add S.hF (by decide)) (aligned_add S.hF (by decide))
    (frame_sep (.inr (by decide)) (by decide) (by decide))
    (by rw [e8]; exact S.sB.sub (c := 0xD8) (l := 4 * 32) (by decide))
    (by simp +decide only [upd_app, ↓reduceIte]; rw [sp5]; rfl)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [sp5]; rfl)
    (by simp +decide only [upd_app, ↓reduceIte])
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords Ml (F + BitVec.ofNat 32 0xD8) (F + BitVec.ofNat 32 0x58) 32 = Mc := ⟨_, rfl⟩
  rw [hMc] at u7
  have frMc : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → Mc x = M0 x := fun x h1 h2 => by
    rw [← hMc, copyWords_outside 32 (h1.sub (c := 0xD8) (l := 4 * 32) (by decide)), frMl x h1 h2]
  have E7 : ∀ q, q.val ∈ [2, 3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 26, 27] → reg m7 q = reg m5 q := fun q hq => by
    have h : q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ ra ∧
        q.val ≠ 0 ∧ q ≠ a0 := by revert q; decide
    rw [k7 q h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1]
    simp only [upd_app, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2, h.1, h.2.1, ite_false]
  have sp7 : reg m7 sp = F := (E7 sp (by decide)).trans sp5
  -- 0x108: `memset` of the array's last 512 bytes
  have hc7 := S.cIn frMc S.code S.sC S.stC (Nat.le_refl _)
  obtain ⟨m8, c8, u8⟩ := St.block s5Zero u7 hc7 s5Zero_end (by simp [BlockOk, BInstr.ok, s5Zero])
  simp only [runBlock, BInstr.run, s5Zero] at u8
  obtain ⟨m9, c9, pc9, mem9, regs9⟩ := u8.self.callRa hc7 s5_at_112 s5_at_116
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P S.hP 0x544 (by decide))
  have r9 := PEnv.reg1 regs9 u8.self.zero
  have x8 : reg m8 8 = F + BitVec.ofNat 32 0x158 := by
    rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7]; rfl
  obtain ⟨m10, c10, pc10, mem10, a010, k10⟩ := memset_correct m9 (P + 0x544) (P + BitVec.ofNat 32 (0x112 + 8))
    (F + BitVec.ofNat 32 0x158) 0 0x200
    (fun i hi => by rw [mem9]; exact S.cIn frMc S.mset S.sZ S.stZ (Nat.le_refl _) i hi)
    (even_at P S.hP 0x544 (by decide)) pc9
    (by rw [r9 a0 (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7]; exact BitVec.zero_add _)
    (by rw [r9 a1 (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [r9 a2 (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [show reg m7 x0 = 0 from u7.zero]; rfl)
    (by rw [regs9]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P S.hP (0x112 + 8) (by decide)))
    (by rw [frame_toNat5 hFw (by decide)]; omega)
    (S.sZ.sub (c := 0x158) (l := 0x200) (by decide))
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillBytes Mc (F + BitVec.ofNat 32 0x158) ((0 : Word).extractLsb' 0 8) 0x200 = Mz :=
    ⟨_, rfl⟩
  rw [mem9, hMz] at mem10
  have s10 : St Mz P m10 0x11A (reg m10) := ⟨by rw [pc10], mem10, fun _ => rfl⟩
  have frMz : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → Mz x = M0 x := fun x h1 h2 => by
    rw [← hMz, fillBytes_sep (h1.sub (c := 0x158) (l := 0x200) (by decide)) (Nat.le_refl _), frMc x h1 h2]
  have E10 : ∀ q, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 26, 27] → reg m10 q = reg m q := fun q hq => by
    have h : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ 8 ∧ q ≠ a0 ∧ q ≠ a1 ∧
        q.val ∈ [2, 3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 26, 27] := by revert q; decide
    rw [k10 q h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1, r9 q h.2.2.2.2.2.1, u8.regs]
    simp only [upd_app, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.1,
      ite_false]
    rw [E7 q h.2.2.2.2.2.2.2.2.2.2, E5 q hq]
  have x10 : reg m10 8 = F + BitVec.ofNat 32 0x158 := by
    rw [k10 8 (by decide) (by decide) (by decide) (by decide) (by decide), r9 8 (by decide), x8]
  -- the schedule
  have win : ∀ s, s < 16 → WIn Mz F (s5W M0 cur) s := fun s hs => by
    have hz : ∀ c, c < 2 → memLoad32 Mz (wslot F s + BitVec.ofNat 32 (4 * c)) =
        memLoad32 Ml (bslot F s + BitVec.ofNat 32 (4 * c)) := fun c hc => by
      rw [← hMz, load_congr (fun x hx => fillBytes_sep hx (Nat.le_refl _))
        (by unfold wslot; rw [add_ofNat_assoc]; exact frame_sep (.inr (by omega)) (by omega) (by omega)),
        show wslot F s + BitVec.ofNat 32 (4 * c) = F + BitVec.ofNat 32 0xD8 + BitVec.ofNat 32 (4 * (2 * s + c)) by
          unfold wslot; rw [add_ofNat_assoc, add_ofNat_assoc]; congr 2; omega,
        ← hMc, copyWords_load 32 (2 * s + c) (by omega) (by rw [frame_toNat5 hFw (by decide)]; omega),
        show bslot F s + BitVec.ofNat 32 (4 * c) = F + BitVec.ofNat 32 0x58 + BitVec.ofNat 32 (4 * (2 * s + c)) by
          unfold bslot; rw [add_ofNat_assoc, add_ofNat_assoc]; congr 2; omega]
    have b := L16.buf s hs
    refine ⟨?_, ?_⟩
    · have := hz 0 (by omega); rw [add_ofNat_zero, add_ofNat_zero] at this; rw [this]; exact b.1
    · exact (hz 1 (by omega)).trans b.2
  obtain ⟨m11, Mw, c11, I11⟩ := s5_sched (w := s5W M0 cur) ⟨S.hP, S.hF, hFw, S.sC.sub (by decide)⟩ (s5W_rec M0 cur)
    s10 (S.cIn frMz S.code S.sC S.stC (Nat.le_refl _)) x10 win
  have frMw : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → Mw x = M0 x := fun x h1 h2 => by
    rw [I11.fr x (h1.sub (c := 0x158) (l := 0x200) (by decide)), frMz x h1 h2]
  have E11 : ∀ q, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 26, 27] → reg m11 q = reg m q := fun q hq => by
    have h : s5SchKeep q = true := by revert q; decide
    rw [I11.keep q h, E10 q hq]
  have sp11 : reg m11 sp = F := (E11 sp (by decide)).trans O.rsp
  have mid : ∀ x, Sep (F + BitVec.ofNat 32 0x58) 0x300 x 1 → Mw x = M1 x := fun x hx => by
    have e1 : Sep (F + BitVec.ofNat 32 0x158) 0x200 x 1 := by
      have := hx.sub (c := 0x100) (l := 0x200) (by decide); rwa [add_ofNat_assoc] at this
    have e2 : Sep (F + BitVec.ofNat 32 0xD8) (4 * 32) x 1 := by
      have := hx.sub (c := 0x80) (l := 4 * 32) (by decide); rwa [add_ofNat_assoc] at this
    have e3 : Sep (F + BitVec.ofNat 32 0x58) 0x80 x 1 := by
      have := hx.sub (c := 0) (l := 0x80) (by decide); rwa [add_ofNat_zero] at this
    rw [I11.fr x e1, ← hMz, fillBytes_sep e1 (Nat.le_refl _), ← hMc, copyWords_outside 32 e2, L16.fr x e3]
  have slot : ∀ c : Nat, c + 4 ≤ 0x58 → (c + 4 ≤ 0x34 ∨ 0x38 ≤ c) →
      memLoad32 Mw (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [low_load hFw mid h1, ← hM1, show (F + 0x34 : Word) = F + BitVec.ofNat 32 0x34 from rfl,
      memLoad32_store32_sep (frame_sep (c := 0x34) (n := 4) (by omega) (by decide) (by omega))]
  -- 0x1F0: the round setup
  obtain ⟨P1, P30, P29, P25, Pa2, Pa3, Pa0, Pra, Pa6, P17, P21, P6, P5, P19, P20, P18, P28, P7, Pk⟩ :=
    s5Pre_run (M := Mw) (f := reg m11) sp11
  obtain ⟨m12, c12, u12⟩ := St.block s5Pre I11.st I11.code s5Pre_end (s5Pre_ok sp11 S.hF S.sC)
  rw [P1] at u12
  obtain ⟨Mp, hMp⟩ : ∃ Mp, s5PreMem Mw F (reg m11) = Mp := ⟨_, rfl⟩
  rw [hMp] at u12
  have preFr : ∀ x, Sep F 0x58 x 1 → Mp x = Mw x := fun x h1 => by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [st_get_sep h1]
  have frMp : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → Mp x = M0 x := fun x h1 h2 => by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [st_get_sep h1]; exact frMw x h1 h2
  have winP : ∀ s, s < 80 → WIn Mp F (s5W M0 cur) s := fun s hs => by
    have w := I11.win s hs
    have q0 : Sep F 0x58 (wslot F s) 4 := by
      have := frame_sep (F := F) (c := 0) (n := 0x58) (d := 0xD8 + 8 * s) (k := 4) (.inl (by omega)) (by omega)
        (by omega)
      rwa [add_ofNat_zero] at this
    have q4 : Sep F 0x58 (wslot F s + 4) 4 := by
      have := frame_sep (F := F) (c := 0) (n := 0x58) (d := 0xD8 + 8 * s + 4) (k := 4) (.inl (by omega))
        (by omega) (by omega)
      rw [add_ofNat_zero, ← add_ofNat_assoc] at this; exact this
    exact ⟨(load_congr preFr q0).trans w.1, (load_congr preFr q4).trans w.2⟩
  have e12 : ∀ q, s5PreKeep q = true → q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 26, 27] →
      reg m12 q = reg m q := fun q h1 h2 => by rw [u12.regs, Pk q h1, E11 q h2]
  have R0 : S5R P F (s5W M0 cur) hv (reg m) 0 Mp m12 := by
    refine ⟨u12.self, S.cIn frMp S.code S.sC S.stC (Nat.le_refl _),
      S.cIn frMp S.kd S.sK S.stK (Nat.le_of_eq sha512KData_len), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, winP, fun q hq => e12 q (by revert q; decide) (by revert q; decide)⟩
    · rw [u12.regs, P29]; rfl
    · rw [u12.regs, P25]; exact (add_ofNat_zero _).symm
    · rw [u12.regs, P30]; rfl
    · rw [e12 23 rfl (by decide), O.al]; rfl
    · rw [u12.regs, Pa0, E11 19 (by decide), O.ah]; rfl
    · rw [u12.regs, P28, E11 22 (by decide), O.bl]; rfl
    · rw [u12.regs, P7, E11 27 (by decide), O.bh]; rfl
    · rw [u12.regs, P18, E11 24 (by decide), O.cl]; rfl
    · rw [e12 26 rfl (by decide), O.ch]; rfl
    · rw [u12.regs, P19, E11 18 (by decide), O.dl]; rfl
    · rw [u12.regs, P20]; exact (slot 0x54 (by decide) (by decide)).trans O.dh
    · rw [u12.regs, Pa2, E11 20 (by decide), O.el]; rfl
    · rw [u12.regs, Pa3]; exact (slot 0x4C (by decide) (by decide)).trans O.eh
    · rw [u12.regs, P6]; exact (slot 0x50 (by decide) (by decide)).trans O.fl
    · rw [u12.regs, P5]; exact (slot 0x44 (by decide) (by decide)).trans O.fh
    · rw [u12.regs, P17]; exact (slot 0x48 (by decide) (by decide)).trans O.gl
    · rw [u12.regs, P21]; exact (slot 0x3C (by decide) (by decide)).trans O.gh
    · rw [u12.regs, Pra]; exact (slot 0x40 (by decide) (by decide)).trans O.hl
    · rw [u12.regs, Pa6]; exact (slot 0x38 (by decide) (by decide)).trans O.hh
  -- the rounds
  obtain ⟨m13, c13, R80⟩ := s5_rounds_from S.hP S.hF 80 0 Mp m12 rfl R0
  obtain ⟨m14, c14, u14, Eal, Eah, Ebl, Ebh, Ecl, Ech, Edl, Edh, Eel, Eeh, Efl, Efh, Egl, Egh, Ehl, Ehh, k14⟩ :=
    s5_rounds_exit R80
  have sp14 : reg m14 sp = F := by rw [k14 sp rfl, O.rsp]
  have mst' : memLoad32 Mp (F + 0xC) = stp := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0xC (by decide) (by decide)).trans O.mst
  have hv30 : memLoad32 Mp (F + 0x30) = lo64 hv.a := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit, ls_same]; rw [E11 23 (by decide), O.al]
  have hv1C : memLoad32 Mp (F + 0x1C) = hi64 hv.a := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit, ls_same]; rw [E11 19 (by decide), O.ah]
  have hv2C : memLoad32 Mp (F + 0x2C) = lo64 hv.b := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit, ls_same]; rw [E11 22 (by decide), O.bl]
  have hv18 : memLoad32 Mp (F + 0x18) = hi64 hv.b := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_same]; rw [E11 27 (by decide), O.bh]
  have hv28 : memLoad32 Mp (F + 0x28) = lo64 hv.c := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit, ls_same]; rw [E11 24 (by decide), O.cl]
  have hv20 : memLoad32 Mp (F + 0x20) = hi64 hv.c := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit, ls_same]; rw [E11 26 (by decide), O.ch]
  have hv24 : memLoad32 Mp (F + 0x24) = lo64 hv.d := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit, ls_same]; rw [E11 18 (by decide), O.dl]
  have hv54 : memLoad32 Mp (F + 0x54) = hi64 hv.d := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0x54 (by decide) (by decide)).trans O.dh
  have hv14 : memLoad32 Mp (F + 0x14) = lo64 hv.e := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit, ls_same]; rw [E11 20 (by decide), O.el]
  have hv4C : memLoad32 Mp (F + 0x4C) = hi64 hv.e := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0x4C (by decide) (by decide)).trans O.eh
  have hv50 : memLoad32 Mp (F + 0x50) = lo64 hv.f := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0x50 (by decide) (by decide)).trans O.fl
  have hv44 : memLoad32 Mp (F + 0x44) = hi64 hv.f := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0x44 (by decide) (by decide)).trans O.fh
  have hv48 : memLoad32 Mp (F + 0x48) = lo64 hv.g := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0x48 (by decide) (by decide)).trans O.gl
  have hv3C : memLoad32 Mp (F + 0x3C) = hi64 hv.g := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0x3C (by decide) (by decide)).trans O.gh
  have hv40 : memLoad32 Mp (F + 0x40) = lo64 hv.h := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0x40 (by decide) (by decide)).trans O.hl
  have hv38 : memLoad32 Mp (F + 0x38) = hi64 hv.h := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]; exact (slot 0x38 (by decide) (by decide)).trans O.hh
  have nx34 : memLoad32 Mp (F + 0x34) = bp + BitVec.ofNat 32 (128 * (j + 1)) := by
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]
    rw [show (F + 0x34 : Word) = F + BitVec.ofNat 32 0x34 from rfl, low_load hFw mid (by decide), ← hM1]
    refine (memLoad32_store32_same M (F + 0x34) _).trans ?_
    rw [hcur]
    show bp + BitVec.ofNat 32 (128 * j) + BitVec.ofNat 32 0x80 = _
    rw [add_ofNat_assoc]; congr 2
  -- 0x376: the feed-forward
  obtain ⟨F1, F23, F19, F22, F27, F24, F26, F18, F20, F21, Fk⟩ :=
    s5Final_run (M := Mp) (f := reg m14) sp14 mst' S.stF
  have hc14 := S.cIn frMp S.code S.sC S.stC (Nat.le_refl _)
  obtain ⟨m15, c15, u15⟩ := St.block s5Final u14 hc14 s5Final_end
    (s5Final_ok sp14 mst' S.hF S.hstp S.sC S.stC)
  simp only [hv30, hv1C, hv2C, hv18, hv28, hv20, hv24, hv54, hv14, hv4C, hv50, hv44, hv48, hv3C, hv40, hv38,
    Eal, Eah, Ebl, Ebh, Ecl, Ech, Edl, Edh, Eel, Eeh, Efl, Efh, Egl, Egh, Ehl, Ehh] at F1 F23 F19 F22 F27 F24 F26 F18 F20
  generalize Sha512.vs (s5W M0 cur) hv 80 = v at F1 F23 F19 F22 F27 F24 F26 F18 F20 ⊢
  obtain ⟨A1, A2⟩ := add64_pair (X := hv.a) (Y := v.a) rfl rfl rfl
  obtain ⟨B1, B2⟩ := add64_pair (X := hv.b) (Y := v.b) rfl rfl rfl
  obtain ⟨C1, C2⟩ := add64_pair (X := hv.c) (Y := v.c) rfl rfl rfl
  obtain ⟨D1, D2⟩ := add64_pair (X := hv.d) (Y := v.d) rfl rfl rfl
  obtain ⟨G1, G2⟩ := add64_pair (X := hv.e) (Y := v.e) rfl rfl rfl
  obtain ⟨H1, H2⟩ := add64_pair (X := hv.f) (Y := v.f) rfl rfl rfl
  obtain ⟨I1, I2⟩ := add64_pair (X := hv.g) (Y := v.g) rfl rfl rfl
  obtain ⟨J1, J2⟩ := add64_pair (X := hv.h) (Y := v.h) rfl rfl rfl
  rw [A2, A1, B2, B1, C2, C1, D2, D1, G2, G1, H2, H1, I2, I1, J2, J1] at F1
  rw [A1] at F23; rw [A2] at F19; rw [B1] at F22; rw [B2] at F27; rw [C1] at F24; rw [C2] at F26; rw [D1] at F18
  rw [G1] at F20
  rw [F1] at u15
  obtain ⟨Mf, hMf⟩ : ∃ Mf, s5FinalMem Mp F stp (lo64 (hv.a + v.a)) (hi64 (hv.a + v.a)) (lo64 (hv.b + v.b))
      (hi64 (hv.b + v.b)) (lo64 (hv.c + v.c)) (hi64 (hv.c + v.c)) (lo64 (hv.d + v.d)) (hi64 (hv.d + v.d))
      (lo64 (hv.e + v.e)) (hi64 (hv.e + v.e)) (lo64 (hv.f + v.f)) (hi64 (hv.f + v.f)) (lo64 (hv.g + v.g))
      (hi64 (hv.g + v.g)) (lo64 (hv.h + v.h)) (hi64 (hv.h + v.h)) = Mf := ⟨_, rfl⟩
  rw [hMf] at u15
  have frMf : ∀ x, Sep F 0x390 x 1 → Sep stp 128 x 1 → Mf x = M0 x := fun x h1 h2 => by
    rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [st_get_sep h1, st_get_sep h2]; exact frMp x h1 h2
  obtain ⟨m16, d16, u16⟩ := u15.jump (S.cIn frMf S.code S.sC S.stC (Nat.le_refl _)) s5_at_43c (off' := 0x82)
    (by decide) (pc_even (off' := 0x82) S.hP u15.pc (by decide) (by decide))
  have kk : ∀ q, s5Keep q = true → reg m16 q = g q := fun q hq => by
    have h1 : s5FinalKeep q = true := by revert q; decide
    have h2 : s5RKeep q = true := by revert q; decide
    rw [u16.regs, Fk q h1, k14 q h2, O.keep q hq]
  refine ⟨m16, Mf, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (.cons d16 (.refl _)))))))))))))))),
    ⟨u16.self, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, kk⟩⟩
  · rw [u16.regs, Fk sp rfl, sp14]
  · rw [u16.regs, F21, nx34]
  · rw [u16.regs, F23]; rfl
  · rw [u16.regs, F19]; rfl
  · rw [u16.regs, F22]; rfl
  · rw [u16.regs, F27]; rfl
  · rw [u16.regs, F24]; rfl
  · rw [u16.regs, F26]; rfl
  · rw [u16.regs, F18]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [u16.regs, F20]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; exact mst'
  · rw [← hMf]; unfold s5FinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]
    rw [← hMp]; unfold s5PreMem; simp (disch := decide) only [ls_lit]
    exact (slot 0x10 (by decide) (by decide)).trans O.mend
  · rw [← hMf]; unfold s5Hv s5FinalMem
    simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF.symm]
    simp only [pk_lohi]; rfl
  · intro x h1 h2
    rw [← hMf]; unfold s5FinalMem
    simp (disch := decide) only [st_get_sep h1, st_get_sep h2]
    rw [← hMp]; unfold s5PreMem
    simp (disch := decide) only [st_get_sep h1]
    have e1 : Sep (F + BitVec.ofNat 32 0x58) 0x300 x 1 := by
      have := h1.sub (c := 0x58) (l := 0x300) (by decide); exact this
    rw [mid x e1, ← hM1, st_get_sep h1 (by decide), O.sv x h1 h2]
  · intro x h1 h2
    exact frMf x h1 h2

end C3.RV32
