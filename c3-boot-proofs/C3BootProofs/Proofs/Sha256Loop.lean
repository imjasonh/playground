import C3BootProofs.Proofs.Sha256LoopFrame

/-!
# `sha2::sha256::compress256`, compact backend, end to end

The outer loop at 0x54 runs once per 64-byte block: it loads the block's
big-endian words into the buffer at `F + 0x6C`, copies them into the
schedule window at `F + 0x2C`, runs the 64 rounds, and adds the working
variables into the state at `stp`. `kcCompress_correct` composes it with
the prologue and the epilogue.
-/

namespace C3.RV32

open C3.Image

/-- The registers `compress256` never writes. -/
def kcKeep (q : Fin 32) : Bool := q.val == 3 || q.val == 4

/-- What the function needs and doesn't change: its code and its callees'
at their offsets from an even `P`, the round constants, the aligned state at
`stp`, the `n` blocks at `bp`, and the frame `F`, all apart where they
must be. -/
structure KCOS (P F stp bp : Word) (n : Nat) (M0 : Word → BitVec 8) : Prop where
  hP : P.toNat % 2 = 0
  hF : F.toNat % 4 = 0
  hFw : F.toNat + 0xE0 ≤ 2 ^ 32
  hstp : stp.toNat % 4 = 0
  hwbp : bp.toNat + 64 * n < 2 ^ 32
  code : CodeIn M0 P sha256CompressCode
  idx : CodeIn M0 (P + 0x25A) rangeFromIndexCode
  stub : CodeIn M0 (P + 0x81C) memcpyStubCode
  body : CodeIn M0 (P + 0x824) memcpyBodyCode
  kd : CodeIn M0 kcK shaKData
  sC : Sep F 0xE0 P sha256CompressCode.length
  sI : Sep F 0xE0 (P + 0x25A) rangeFromIndexCode.length
  sU : Sep F 0xE0 (P + 0x81C) memcpyStubCode.length
  sB : Sep F 0xE0 (P + 0x824) memcpyBodyCode.length
  sK : Sep F 0xE0 kcK 256
  stC : Sep stp 32 P sha256CompressCode.length
  stI : Sep stp 32 (P + 0x25A) rangeFromIndexCode.length
  stU : Sep stp 32 (P + 0x81C) memcpyStubCode.length
  stB : Sep stp 32 (P + 0x824) memcpyBodyCode.length
  stK : Sep stp 32 kcK 256
  stF : Sep stp 32 F 0xE0
  bF : Sep bp (64 * n) F 0xE0
  bSt : Sep bp (64 * n) stp 32

theorem KCOS.cIn {P F stp bp : Word} {n : Nat} {M0 M : Word → BitVec 8} (_ : KCOS P F stp bp n M0)
    (fr : ∀ x, Sep F 0xE0 x 1 → Sep stp 32 x 1 → M x = M0 x) {b : Word} {code : List Nat} {k : Nat}
    (hc : CodeIn M0 b code) (h1 : Sep F 0xE0 b k) (h2 : Sep stp 32 b k) (hk : code.length ≤ k) :
    CodeIn M b code := fun i hi => by
  rw [fr _ (h1.subR (c := i) (l := 1) (by omega)) (h2.subR (c := i) (l := 1) (by omega))]; exact hc i hi

set_option maxRecDepth 20000 in
theorem shaKData_length : shaKData.length = 256 := rfl

/-- What holds at 0x54 before block `j`, with the state `hv` after `j`
blocks: `Ms` holds the registers the prologue saved, and `g` is the
register file at entry. -/
structure KCO (P F stp bp : Word) (n : Nat) (M0 Ms : Word → BitVec 8) (g : Fin 32 → Word) (j : Nat)
    (hv : Sha256.V8) (M : Word → BitVec 8) (m : Machine) : Prop where
  st : St M P m 0x54 (reg m)
  rsp : reg m sp = F
  r9 : reg m 9 = bp + BitVec.ofNat 32 (64 * j)
  r18 : reg m 18 = stp
  r19 : reg m 19 = 0x10
  r20 : reg m 20 = F + 0x2C
  r21 : reg m 21 = 3
  r27 : reg m 27 = F + 0x6C
  va : reg m 23 = hv.a
  vd : reg m 25 = hv.d
  ve : reg m 26 = hv.e
  vh : reg m 24 = hv.h
  mb : memLoad32 M (F + 0x28) = hv.b
  mc : memLoad32 M (F + 0x24) = hv.c
  mf : memLoad32 M (F + 0x20) = hv.f
  mg : memLoad32 M (F + 0x1C) = hv.g
  m8 : memLoad32 M (F + 0x8) = bp + BitVec.ofNat 32 (64 * n)
  hst : wordsAt M stp 8 = hv.toList
  sv : ∀ x, Sep F 0xAC x 1 → Sep stp 32 x 1 → M x = Ms x
  fr : ∀ x, Sep F 0xE0 x 1 → Sep stp 32 x 1 → M x = M0 x
  keep : ∀ q, kcKeep q = true → reg m q = g q

/-- The state plus the working variables, section 6.2.2 step 4. -/
def kcAdd (hv v : Sha256.V8) : Sha256.V8 :=
  ⟨hv.a + v.a, hv.b + v.b, hv.c + v.c, hv.d + v.d, hv.e + v.e, hv.f + v.f, hv.g + v.g, hv.h + v.h⟩

theorem kcAdd_toList (hv v : Sha256.V8) :
    (kcAdd hv v).toList = List.zipWith (· + ·) hv.toList v.toList := rfl

/-- The block's schedule as a function. -/
abbrev kcW (M0 : Word → BitVec 8) (cur : Word) : Nat → Word :=
  fun t => (Sha256.schedule (memBytes M0 cur 64))[t]!

theorem kcW_sched (M0 : Word → BitVec 8) (cur : Word) : ShaSched (kcW M0 cur) :=
  fun _ h1 h2 => Sha256.sched_rec _ h1 h2

theorem load_congr {M M' : Word → BitVec 8} {a b : Word} {n : Nat} (hfr : ∀ x, Sep a n x 1 → M' x = M x)
    (h : Sep a n b 4) : memLoad32 M' b = memLoad32 M b :=
  memLoad32_congr fun j hj => hfr _ (h.subR (c := j) (l := 1) (by omega))

theorem frame_sep {F : Word} {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (h1 : c + n ≤ 2 ^ 32)
    (h2 : d + k ≤ 2 ^ 32) : Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 d) k :=
  sep_offsets F h h1 h2

theorem beq_blocks {bp : Word} {j n : Nat} (hj : j < n) (hw : bp.toNat + 64 * n < 2 ^ 32) :
    branchTaken .beq (bp + BitVec.ofNat 32 (64 * j)) (bp + BitVec.ofNat 32 (64 * n)) = false := by
  unfold branchTaken
  rw [beq_eq_false_iff_ne]
  exact add_ofNat_ne bp (by omega) (by omega) (by omega)

/-- The registers that hold their value from the top of the outer loop to
the start of the rounds. -/
def kcMid (q : Fin 32) : Bool := q.val ∈ [2, 3, 4, 18, 19, 20, 21, 23, 24, 25, 26, 27]

theorem frame_toNat {F : Word} (hFw : F.toNat + 0xE0 ≤ 2 ^ 32) {c : Nat} (hc : c < 0xE0) :
    (F + BitVec.ofNat 32 c).toNat = F.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

theorem sep_shrink {F x : Word} {n n' : Nat} (h : Sep F n x 1) (hn : n' ≤ n) : Sep F n' x 1 := by
  have := h.sub (c := 0) (l := n') (by omega)
  rwa [add_ofNat_zero] at this

theorem kcMid_load : ∀ q, kcMid q = true → kcLoadKeep q = true := by decide
theorem kcKeep_final : ∀ q, kcKeep q = true → kcFinalKeep q = true := by decide
theorem kcKeep_loop : ∀ q, kcKeep q = true → kcLoopKeep q = true := by decide
theorem kcKeep_mid : ∀ q, kcKeep q = true → kcMid q = true := by decide
theorem kcKeep_pre : ∀ q, kcKeep q = true → kcPreKeep q = true := by decide

set_option maxHeartbeats 16000000 in
/-- One block, from 0x54 back to 0x54. -/
theorem kc_block {P F stp bp : Word} {n j : Nat} {M0 Ms M : Word → BitVec 8} {g : Fin 32 → Word}
    {hv : Sha256.V8} {m : Machine} {cur : Word} (S : KCOS P F stp bp n M0) (O : KCO P F stp bp n M0 Ms g j hv M m)
    (hj : j < n) (hcur : cur = bp + BitVec.ofNat 32 (64 * j)) :
    ∃ m' M', Steps m m' ∧ KCO P F stp bp n M0 Ms g (j + 1) (kcAdd hv (Sha256.vs (kcW M0 cur) hv 64)) M' m' := by
  have hc0 := S.cIn O.fr S.code S.sC S.stC (Nat.le_refl _)
  have hi0 := S.cIn O.fr S.idx S.sI S.stI (Nat.le_refl _)
  -- 0x54: the end of the blocks, and the exit test
  obtain ⟨m1, d1, u1⟩ := O.st.lw hc0 kc_at_54 (off' := 0x56) (by decide)
    (by rw [O.rsp]; exact fr_al S.hF (by decide))
  rw [O.rsp, O.m8] at u1
  obtain ⟨m2, d2, u2⟩ := u1.notTaken hc0 0x5A kc_at_56 (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [O.r9]; exact beq_blocks hj S.hwbp)
  obtain ⟨m3, c3, u3⟩ := St.block kcBlkA u2 hc0 kcBlkA_end (by simp [BlockOk, BInstr.ok, kcBlkA])
  simp only [runBlock, BInstr.run, kcBlkA] at u3
  have e3 : ∀ q, kcMid q = true → reg m3 q = reg m q := fun q hq => by
    rw [u3.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl]
  have x8_3 : reg m3 8 = BitVec.ofNat 32 (4 * 0) := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
  have x22_3 : reg m3 22 = cur + 0x40 := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [O.r9, hcur]; rfl
  have x9_3 : reg m3 9 = cur := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [O.r9, hcur]
  -- the load loop
  have sBuf : Sep (F + BitVec.ofNat 32 0x6C) 0x40 cur 64 := by
    rw [hcur]; exact (S.bF.symm.sub (c := 0x6C) (l := 0x40) (by decide)).subR (c := 64 * j) (l := 64) (by omega)
  have blk : ∀ i, i < 64 → M (cur + BitVec.ofNat 32 i) = M0 (cur + BitVec.ofNat 32 i) := fun i hi => by
    rw [hcur, add_ofNat_assoc]
    exact O.fr _ (S.bF.symm.subR (c := 64 * j + i) (l := 1) (by omega))
      (S.bSt.symm.subR (c := 64 * j + i) (l := 1) (by omega))
  have LS : KCLStatic P F cur M0 M :=
    ⟨S.hP, S.hF, S.sC.sub (by decide), S.sI.sub (by decide), sBuf, blk⟩
  have L0 : KCL P F cur M0 M (reg m3) 0 M m3 :=
    ⟨u3.self, hc0, hi0, x8_3, x9_3, (e3 _ rfl).trans O.r21, (e3 _ rfl).trans O.r27,
      fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨m4, Ml, c4, L16⟩ := kc_load_from LS 16 0 M m3 rfl L0
  obtain ⟨m5, c5, u5, k5⟩ := kc_load_exit L16
  have frMl : ∀ x, Sep F 0xE0 x 1 → Sep stp 32 x 1 → Ml x = M0 x := fun x h1 h2 => by
    rw [L16.fr x (h1.sub (c := 0x6C) (l := 0x40) (by decide)), O.fr x h1 h2]
  have e5 : ∀ q, kcMid q = true → reg m5 q = reg m q := fun q hq => by
    rw [k5 q (kcMid_load q hq), e3 q hq]
  have sp5 : reg m5 sp = F := (e5 sp rfl).trans O.rsp
  -- 0xA0: the next block's address, and `memcpy`'s arguments
  obtain ⟨m6, c6, u6⟩ := St.block kcCopy u5 L16.code kcCopy_end (kcCopy_ok sp5 S.hF S.sC)
  simp only [runBlock, BInstr.run, kcCopy] at u6
  rw [sp5, k5 22 rfl, x22_3] at u6
  obtain ⟨Mc0, hMc0⟩ : ∃ Mc0, memStore32 Ml (F + 0xC) (cur + 0x40) = Mc0 := ⟨_, rfl⟩
  rw [hMc0] at u6
  have frMc0 : ∀ x, Sep F 0xE0 x 1 → Sep stp 32 x 1 → Mc0 x = M0 x := fun x h1 h2 => by
    rw [← hMc0, st_get_sep h1 (by decide), frMl x h1 h2]
  have e8 : P + 0x81C + 8 = P + 0x824 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m7, c7, u7, a07, k7⟩ := St.memcpyW (B := P + 0x81C) (w := 16)
    (dst := F + BitVec.ofNat 32 0x2C) (src := F + BitVec.ofNat 32 0x6C)
    (even_at P S.hP 0x81C (by decide)) u6.self (S.cIn frMc0 S.code S.sC S.stC (Nat.le_refl _))
    (S.cIn frMc0 S.stub S.sU S.stU (Nat.le_refl _)) (by rw [e8]; exact S.cIn frMc0 S.body S.sB S.stB (Nat.le_refl _))
    kc_at_ae kc_at_b2 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P S.hP (0xAE + 8) (by decide))
    (by decide) (by have := S.hFw; rw [frame_toNat S.hFw (by decide)]; omega) (by decide)
    (aligned_add S.hF (by decide)) (aligned_add S.hF (by decide))
    (frame_sep (.inl (by decide)) (by decide) (by decide))
    (by rw [e8]; exact S.sB.sub (c := 0x2C) (l := 4 * 16) (by decide))
    (by rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rfl)
    (by rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte])
  obtain ⟨Mc, hMc⟩ : ∃ Mc, copyWords Mc0 (F + BitVec.ofNat 32 0x2C) (F + BitVec.ofNat 32 0x6C) 16 = Mc :=
    ⟨_, rfl⟩
  rw [hMc] at u7
  have frMc : ∀ x, Sep F 0xE0 x 1 → Sep stp 32 x 1 → Mc x = M0 x := fun x h1 h2 => by
    rw [← hMc, copyWords_outside 16 (h1.sub (c := 0x2C) (l := 4 * 16) (by decide)), frMc0 x h1 h2]
  have e7 : ∀ q, kcMid q = true → reg m7 q = reg m q := fun q hq => by
    have k := fun r (hr : kcMid r = false) => pkeep_ne hq hr
    rw [k7 q (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl) (k t0 rfl) (k t1 rfl)
      (k ra rfl), u6.regs, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, e5 q hq]
  have sp7 : reg m7 sp = F := (e7 sp rfl).trans O.rsp
  -- frame words below the window, through the copy and the store at `F + 0xC`
  have slotC : ∀ c : Nat, c + 4 ≤ 0x2C → (c + 4 ≤ 0xC ∨ 0x10 ≤ c) →
      memLoad32 Mc (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [← hMc, copyWords_load_sep (frame_sep (.inr (by omega)) (by decide) (by omega)), ← hMc0,
      show (F + 0xC : Word) = F + BitVec.ofNat 32 0xC from rfl, memLoad32_store32_sep (frame_sep (c := 0xC) (n := 4) (by omega) (by decide) (by omega)),
      load_congr L16.fr (frame_sep (.inr (by omega)) (by decide) (by omega))]
  -- 0xB6: the round setup
  obtain ⟨P1, P8, P7, Pa0, Pa2, P26, P17, P5, Pa6, P29, Pk⟩ := kcPre_run (M := Mc) (f := reg m7) u7.zero
  obtain ⟨m8, c8, u8⟩ := St.block kcPre u7 (S.cIn frMc S.code S.sC S.stC (Nat.le_refl _)) kcPre_end
    (kcPre_ok sp7 S.hF S.sC)
  rw [P1, sp7] at u8
  obtain ⟨Mp, hMp⟩ : ∃ Mp, memStore32 (memStore32 (memStore32 Mc (F + 0x10) (reg m7 26)) (F + 0x18) (reg m7 23))
      (F + 0x14) (reg m7 25) = Mp := ⟨_, rfl⟩
  rw [hMp] at u8
  have frMp : ∀ x, Sep F 0xE0 x 1 → Sep stp 32 x 1 → Mp x = M0 x := fun x h1 h2 => by
    rw [← hMp, st_get_sep h1 (by decide), st_get_sep h1 (by decide), st_get_sep h1 (by decide), frMc x h1 h2]
  have e8' : ∀ q, kcMid q = true → kcPreKeep q = true → reg m8 q = reg m q := fun q h1 h2 => by
    rw [u8.regs, Pk q h2, e7 q h1]
  have p28 : memLoad32 Mc (F + 0x28) = hv.b := (slotC 0x28 (by decide) (by decide)).trans O.mb
  have p24 : memLoad32 Mc (F + 0x24) = hv.c := (slotC 0x24 (by decide) (by decide)).trans O.mc
  have p20 : memLoad32 Mc (F + 0x20) = hv.f := (slotC 0x20 (by decide) (by decide)).trans O.mf
  have p1C : memLoad32 Mc (F + 0x1C) = hv.g := (slotC 0x1C (by decide) (by decide)).trans O.mg
  have p08 : memLoad32 Mc (F + 0x8) = bp + BitVec.ofNat 32 (64 * n) :=
    (slotC 0x8 (by decide) (by decide)).trans O.m8
  have p0C : memLoad32 Mc (F + 0xC) = cur + 0x40 := by
    show memLoad32 Mc (F + BitVec.ofNat 32 0xC) = _
    rw [← hMc, copyWords_load_sep (k := 16)
      (frame_sep (c := 0x2C) (n := 4 * 16) (d := 0xC) (k := 4) (.inr (by decide)) (by decide) (by decide)), ← hMc0]
    exact memLoad32_store32_same _ _ _
  have KS : KCStatic P F := ⟨S.hP, S.hF, S.sC, S.sK⟩
  have hFw := S.hFw
  have R0 : KCR P F (kcW M0 cur) hv (reg m8) Mp 0 Mp m8 := by
    refine ⟨u8.self, S.cIn frMp S.code S.sC S.stC (Nat.le_refl _),
      S.cIn frMp S.kd S.sK S.stK (Nat.le_of_eq shaKData_length), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · rw [u8.regs, P8]; rfl
    · rw [e8' 19 rfl rfl, O.r19]
    · exact (e8' 20 rfl rfl).trans O.r20
    · rw [u8.regs, Pk 22 rfl, k7 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), u6.regs]
      simp +decide only [upd_app, ↓reduceIte]; rw [sp5]; rfl
    · rw [u8.regs, P7]; exact (add_ofNat_zero _).symm
    · rw [u8.regs, Pa2, e7 23 rfl, O.va]; rfl
    · rw [u8.regs, P29, sp7]; exact p28
    · rw [u8.regs, Pa6, sp7]; exact p24
    · rw [e8' 25 rfl rfl, O.vd]; rfl
    · rw [u8.regs, Pa0, e7 26 rfl, O.ve]; rfl
    · rw [u8.regs, P5, sp7]; exact p20
    · rw [u8.regs, P17, sp7]; exact p1C
    · rw [u8.regs, P26, e7 24 rfl, O.vh]; rfl
    · intro s h1 _
      have hs : s < 16 := by rw [Nat.max_eq_right (Nat.zero_le _)] at h1; exact h1
      unfold kslot
      rw [Nat.mod_eq_of_lt hs, ← hMp, show (F + 0x14 : Word) = F + BitVec.ofNat 32 0x14 from rfl,
        show (F + 0x18 : Word) = F + BitVec.ofNat 32 0x18 from rfl,
        show (F + 0x10 : Word) = F + BitVec.ofNat 32 0x10 from rfl,
        memLoad32_store32_sep (frame_sep (.inl (by omega)) (by decide) (by omega)),
        memLoad32_store32_sep (frame_sep (.inl (by omega)) (by decide) (by omega)),
        memLoad32_store32_sep (frame_sep (.inl (by omega)) (by decide) (by omega)),
        ← add_ofNat_assoc, ← hMc,
        copyWords_load 16 s hs (by rw [frame_toNat S.hFw (by decide)]; omega), add_ofNat_assoc, ← hMc0,
        show (F + 0xC : Word) = F + BitVec.ofNat 32 0xC from rfl,
        memLoad32_store32_sep (frame_sep (.inl (by omega)) (by decide) (by omega)), L16.buf s hs]
  -- the rounds
  obtain ⟨m9, Mr, c9, R64⟩ := kc_rounds_from KS (kcW_sched M0 cur) 64 0 Mp m8 rfl R0
  obtain ⟨m10, c10, u10, Ea, Eb, Ec, Ed, Ee, Ef, Eg, Eh, k10⟩ := kc_rounds_exit R64
  have frMr : ∀ x, Sep F 0xE0 x 1 → Sep stp 32 x 1 → Mr x = M0 x := fun x h1 h2 => by
    rw [R64.fr x (h1.sub (c := 0x2C) (l := 0x40) (by decide)), frMp x h1 h2]
  have Lr : ∀ c, c + 4 ≤ 0x2C → memLoad32 Mr (F + BitVec.ofNat 32 c) = memLoad32 Mp (F + BitVec.ofNat 32 c) :=
    fun c h => load_congr R64.fr (frame_sep (.inr h) (by decide) (by omega))
  have sp10 : reg m10 sp = F := by rw [k10 sp rfl, e8' sp rfl rfl, O.rsp]
  have s18 : reg m10 18 = stp := by rw [k10 18 rfl, e8' 18 rfl rfl, O.r18]
  -- the feed-forward
  obtain ⟨F1, F23, F25, F26, F24, F9, Fk⟩ := kcFinal_run (M := Mr) (f := reg m10) sp10 s18 S.stF
  obtain ⟨m11, c11, u11⟩ := St.block kcFinal u10 (S.cIn frMr S.code S.sC S.stC (Nat.le_refl _)) kcFinal_end
    (kcFinal_ok sp10 s18 S.hF S.hstp S.sC S.stC)
  rw [F1] at u11
  have r18' : memLoad32 Mr (F + 0x18) = hv.a := by
    rw [show (F + 0x18 : Word) = F + BitVec.ofNat 32 0x18 from rfl, Lr 0x18 (by decide), ← hMp]
    simp (disch := decide) only [ls_lit, ls_same]; rw [e7 23 rfl, O.va]
  have r28' : memLoad32 Mr (F + 0x28) = hv.b := by
    rw [show (F + 0x28 : Word) = F + BitVec.ofNat 32 0x28 from rfl, Lr 0x28 (by decide), ← hMp]
    simp (disch := decide) only [ls_lit]; exact p28
  have r24' : memLoad32 Mr (F + 0x24) = hv.c := by
    rw [show (F + 0x24 : Word) = F + BitVec.ofNat 32 0x24 from rfl, Lr 0x24 (by decide), ← hMp]
    simp (disch := decide) only [ls_lit]; exact p24
  have r14' : memLoad32 Mr (F + 0x14) = hv.d := by
    rw [show (F + 0x14 : Word) = F + BitVec.ofNat 32 0x14 from rfl, Lr 0x14 (by decide), ← hMp]
    simp (disch := decide) only [ls_same]; rw [e7 25 rfl, O.vd]
  have r10' : memLoad32 Mr (F + 0x10) = hv.e := by
    rw [show (F + 0x10 : Word) = F + BitVec.ofNat 32 0x10 from rfl, Lr 0x10 (by decide), ← hMp]
    simp (disch := decide) only [ls_lit, ls_same]; rw [e7 26 rfl, O.ve]
  have r20' : memLoad32 Mr (F + 0x20) = hv.f := by
    rw [show (F + 0x20 : Word) = F + BitVec.ofNat 32 0x20 from rfl, Lr 0x20 (by decide), ← hMp]
    simp (disch := decide) only [ls_lit]; exact p20
  have r1C' : memLoad32 Mr (F + 0x1C) = hv.g := by
    rw [show (F + 0x1C : Word) = F + BitVec.ofNat 32 0x1C from rfl, Lr 0x1C (by decide), ← hMp]
    simp (disch := decide) only [ls_lit]; exact p1C
  have r0C' : memLoad32 Mr (F + 0xC) = cur + 0x40 := by
    rw [show (F + 0xC : Word) = F + BitVec.ofNat 32 0xC from rfl, Lr 0xC (by decide), ← hMp]
    simp (disch := decide) only [ls_lit]; exact p0C
  have r08' : memLoad32 Mr (F + 0x8) = bp + BitVec.ofNat 32 (64 * n) := by
    rw [show (F + 0x8 : Word) = F + BitVec.ofNat 32 0x8 from rfl, Lr 0x8 (by decide), ← hMp]
    simp (disch := decide) only [ls_lit]; exact p08
  have h25 : reg m10 25 + memLoad32 Mr (F + 0x14) = hv.d + (Sha256.vs (kcW M0 cur) hv 64).d := by
    rw [Ed, r14', BitVec.add_comm]
  have h24 : reg m10 24 = hv.h := by rw [k10 24 rfl, e8' 24 rfl rfl, O.vh]
  rw [r18', r28', r24', r10', r20', r1C', Ea, Eb, Ec, Ee, Ef, Eg, Eh, h25, h24] at u11
  obtain ⟨Mf, hMf⟩ : ∃ Mf, kcFinalMem Mr F stp (hv.a + (Sha256.vs (kcW M0 cur) hv 64).a)
      (hv.b + (Sha256.vs (kcW M0 cur) hv 64).b) (hv.c + (Sha256.vs (kcW M0 cur) hv 64).c)
      (hv.d + (Sha256.vs (kcW M0 cur) hv 64).d) (hv.e + (Sha256.vs (kcW M0 cur) hv 64).e)
      (hv.f + (Sha256.vs (kcW M0 cur) hv 64).f) (hv.g + (Sha256.vs (kcW M0 cur) hv 64).g)
      (hv.h + (Sha256.vs (kcW M0 cur) hv 64).h) = Mf := ⟨_, rfl⟩
  rw [hMf] at u11
  have hagree : ∀ x, Sep F 0xAC x 1 → Sep stp 32 x 1 → Mf x = M x := fun x h1 h2 => by
    rw [← hMf]
    unfold kcFinalMem
    simp (disch := decide) only [st_get_sep h1, st_get_sep h2]
    rw [R64.fr x (h1.sub (c := 0x2C) (l := 0x40) (by decide)), ← hMp]
    simp (disch := decide) only [st_get_sep h1]
    rw [← hMc, copyWords_outside 16 (h1.sub (c := 0x2C) (l := 4 * 16) (by decide)), ← hMc0,
      st_get_sep h1 (by decide), L16.fr x (h1.sub (c := 0x6C) (l := 0x40) (by decide))]
  have frMf : ∀ x, Sep F 0xE0 x 1 → Sep stp 32 x 1 → Mf x = M0 x := fun x h1 h2 => by
    rw [hagree x (sep_shrink h1 (by decide)) h2, O.fr x h1 h2]
  obtain ⟨m12, d12, u12⟩ := u11.jump (S.cIn frMf S.code S.sC S.stC (Nat.le_refl _)) kc_at_22c (off' := 0x54)
    (by decide) (pc_even (off' := 0x54) S.hP u11.pc (by decide) (by decide))
  refine ⟨m12, Mf, .cons d1 (.cons d2 (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (c11.trans (.cons d12 (.refl _)))))))))))), ⟨u12.self, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 => (hagree x h1 h2).trans (O.sv x h1 h2), frMf, ?_⟩⟩
  · rw [u12.regs, Fk sp rfl, sp10]
  · rw [u12.regs, F9, r0C', hcur, show (0x40 : Word) = BitVec.ofNat 32 64 from rfl, add_ofNat_assoc,
      show 64 * j + 64 = 64 * (j + 1) by omega]
  · rw [u12.regs, Fk 18 rfl, s18]
  · rw [u12.regs, Fk 19 rfl, k10 19 rfl, e8' 19 rfl rfl, O.r19]
  · rw [u12.regs, Fk 20 rfl, k10 20 rfl, e8' 20 rfl rfl, O.r20]
  · rw [u12.regs, Fk 21 rfl, k10 21 rfl, e8' 21 rfl rfl, O.r21]
  · rw [u12.regs, Fk 27 rfl, k10 27 rfl, e8' 27 rfl rfl, O.r27]
  · rw [u12.regs, F23, r18', Ea]; rfl
  · rw [u12.regs, F25, h25]; rfl
  · rw [u12.regs, F26, r10', Ee]; rfl
  · rw [u12.regs, F24, h24, Eh]; rfl
  · rw [← hMf]; unfold kcFinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold kcFinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold kcFinalMem; simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold kcFinalMem; simp (disch := decide) only [ls_same, ls_sep S.stF]; rfl
  · rw [← hMf]; unfold kcFinalMem; simp (disch := decide) only [ls_lit, ls_sep S.stF]; exact r08'
  · rw [← hMf]
    show [memLoad32 _ (stp + BitVec.ofNat 32 0), memLoad32 _ (stp + BitVec.ofNat 32 4),
      memLoad32 _ (stp + BitVec.ofNat 32 8), memLoad32 _ (stp + BitVec.ofNat 32 12),
      memLoad32 _ (stp + BitVec.ofNat 32 16), memLoad32 _ (stp + BitVec.ofNat 32 20),
      memLoad32 _ (stp + BitVec.ofNat 32 24), memLoad32 _ (stp + BitVec.ofNat 32 28)] = _
    unfold kcFinalMem
    simp (disch := decide) only [ls_lit, ls_same, ls_sep S.stF.symm]
    rfl
  · intro q hq
    rw [u12.regs, Fk q (kcKeep_final q hq), k10 q (kcKeep_loop q hq), e8' q (kcKeep_mid q hq) (kcKeep_pre q hq),
      O.keep q hq]

/-- The state's eight words at `stp`. -/
def kcHv (M : Word → BitVec 8) (stp : Word) : Sha256.V8 :=
  ⟨memLoad32 M (stp + BitVec.ofNat 32 0), memLoad32 M (stp + BitVec.ofNat 32 4),
   memLoad32 M (stp + BitVec.ofNat 32 8), memLoad32 M (stp + BitVec.ofNat 32 12),
   memLoad32 M (stp + BitVec.ofNat 32 16), memLoad32 M (stp + BitVec.ofNat 32 20),
   memLoad32 M (stp + BitVec.ofNat 32 24), memLoad32 M (stp + BitVec.ofNat 32 28)⟩

theorem wordsAt_kcHv (M : Word → BitVec 8) (stp : Word) : wordsAt M stp 8 = (kcHv M stp).toList := rfl

/-- The state after `j` blocks. -/
def kcState (M0 : Word → BitVec 8) (stp bp : Word) : Nat → Sha256.V8
  | 0 => kcHv M0 stp
  | j + 1 => kcAdd (kcState M0 stp bp j)
      (Sha256.vs (kcW M0 (bp + BitVec.ofNat 32 (64 * j))) (kcState M0 stp bp j) 64)

theorem kcState_toList (M0 : Word → BitVec 8) (stp bp : Word) :
    ∀ j, (kcState M0 stp bp j).toList = (blockList M0 bp j).foldl Sha256.compress (wordsAt M0 stp 8)
  | 0 => rfl
  | j + 1 => by
    rw [blockList_succ, List.foldl_append, ← kcState_toList M0 stp bp j, List.foldl_cons, List.foldl_nil,
      Sha256.compress_vs]
    rfl

/-- The outer loop from block `j` to its exit. -/
theorem kc_outer {P F stp bp : Word} {n : Nat} {M0 Ms : Word → BitVec 8} {g : Fin 32 → Word}
    (S : KCOS P F stp bp n M0) :
    ∀ k j (M : Word → BitVec 8) (m : Machine), j + k = n → KCO P F stp bp n M0 Ms g j (kcState M0 stp bp j) M m →
      ∃ m' M', Steps m m' ∧ KCO P F stp bp n M0 Ms g n (kcState M0 stp bp n) M' m'
  | 0, j, M, m, h, O => ⟨m, M, .refl _, by rw [Nat.add_zero] at h; subst h; exact O⟩
  | k + 1, j, M, m, h, O => by
    obtain ⟨m1, M1, c1, O1⟩ := kc_block S O (by omega) rfl
    obtain ⟨m2, M2, c2, O2⟩ := kc_outer S k (j + 1) M1 m1 (by omega) O1
    exact ⟨m2, M2, c1.trans c2, O2⟩

theorem kc_sll6 (bp : Word) (n : Nat) (hn : n < 2 ^ 26) :
    ((BitVec.ofNat 32 n <<< 6) + bp) = bp + BitVec.ofNat 32 (64 * n) := by
  rw [BitVec.add_comm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.mul_comm n 64]

set_option maxRecDepth 20000 in
theorem kcPs_range : ∀ p ∈ kcPs, p.2.toNat % 4 = 0 ∧ 0xAC ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0xE0 := by decide

set_option maxRecDepth 20000 in
theorem kcPs_sp : ∀ p ∈ kcPs, p.1 ≠ sp := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The prologue, from 0x00 to 0x54: the frame, the register saves, and the
outer loop's first state. -/
theorem kc_pro (m : Machine) {P sp0 stp bp : Word} {n : Nat} (S : KCOS P (sp0 + 0xFFFFFF20) stp bp n m.mem)
    (hn : n < 2 ^ 26) (hpc : m.pc = P) (ha0 : reg m a0 = stp) (ha1 : reg m a1 = bp)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hsp : reg m sp = sp0) :
    ∃ m' Ms, Steps m m' ∧ KCO P (sp0 + 0xFFFFFF20) stp bp n m.mem Ms (reg m) 0 (kcHv m.mem stp) Ms m' ∧
      ∀ r o, (r, o) ∈ kcPs → memLoad32 Ms (sp0 + 0xFFFFFF20 + o) = reg m r := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm S.code kc_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF20) sp = sp0 + 0xFFFFFF20 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock kcPs) u1 S.code kcSave_end (saveBlock_ok _ kcPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' S.hF (kcPs_range p hp).1, frm_sep' S.sC (kcPs_range p hp).2.2⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (sp0 + 0xFFFFFF20)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF20)) kcPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside kcPs fun p hp => frm_sep' hx (kcPs_range p hp).2.2
  have k2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q hq => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFF20 := by rw [u2.regs]; exact sp1
  have a02 : reg m2 a0 = stp := (k2 a0 (by decide)).trans ha0
  have cSv : CodeIn Msv P sha256CompressCode := fun i hi => by
    rw [frSv _ (S.sC.subR (c := i) (l := 1) (by omega))]; exact S.code i hi
  obtain ⟨E1, E9, E18, E23, E25, E26, E24, E27, E19, E20, E21, Ek⟩ :=
    kcSetup_run (M := Msv) (f := reg m2) u2.self.zero sp2 a02 S.stF.symm
  obtain ⟨m3, c3, u3⟩ := St.block kcSetup u2.self cSv kcSetup_end (kcSetup_ok sp2 a02 S.hF S.hstp S.sC)
  rw [E1, (k2 a2 (by decide)).trans ha2, (k2 a1 (by decide)).trans ha1, kc_sll6 bp n hn] at u3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, kcSetupMem Msv (sp0 + 0xFFFFFF20) stp (bp + BitVec.ofNat 32 (64 * n)) = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u3
  have stL : ∀ c : Nat, c + 4 ≤ 32 → memLoad32 Msv (stp + BitVec.ofNat 32 c) = memLoad32 m.mem (stp + BitVec.ofNat 32 c) :=
    fun c hc => load_congr frSv (S.stF.symm.subR (c := c) (l := 4) hc)
  have k3 : ∀ q, kcSetupKeep q = true → q ≠ sp → reg m3 q = reg m q := fun q h1 h2 => by
    rw [u3.regs, Ek q h1, k2 q h2]
  refine ⟨m3, Ms, .cons d1 (c2.trans c3), ⟨u3.self, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, fun _ _ _ => rfl, ?_, ?_⟩, ?_⟩
  · rw [u3.regs, Ek sp rfl, sp2]
  · rw [u3.regs, E9, k2 a1 (by decide), ha1, show 64 * 0 = 0 from rfl, add_ofNat_zero]
  · rw [u3.regs, E18]
  · rw [u3.regs, E19]
  · rw [u3.regs, E20]
  · rw [u3.regs, E21]
  · rw [u3.regs, E27]
  · rw [u3.regs, E23]; exact stL 0 (by decide)
  · rw [u3.regs, E25]; exact stL 12 (by decide)
  · rw [u3.regs, E26]; exact stL 16 (by decide)
  · rw [u3.regs, E24]; exact stL 28 (by decide)
  · rw [← hMs]; unfold kcSetupMem; simp (disch := decide) only [ls_lit, ls_same]; exact stL 4 (by decide)
  · rw [← hMs]; unfold kcSetupMem; simp (disch := decide) only [ls_lit, ls_same]; exact stL 8 (by decide)
  · rw [← hMs]; unfold kcSetupMem; simp (disch := decide) only [ls_lit, ls_same]; exact stL 20 (by decide)
  · rw [← hMs]; unfold kcSetupMem; simp (disch := decide) only [ls_lit, ls_same]; exact stL 24 (by decide)
  · rw [← hMs]; unfold kcSetupMem; simp (disch := decide) only [ls_same]
  · rw [← hMs]
    show [memLoad32 _ (stp + BitVec.ofNat 32 0), memLoad32 _ (stp + BitVec.ofNat 32 4),
      memLoad32 _ (stp + BitVec.ofNat 32 8), memLoad32 _ (stp + BitVec.ofNat 32 12),
      memLoad32 _ (stp + BitVec.ofNat 32 16), memLoad32 _ (stp + BitVec.ofNat 32 20),
      memLoad32 _ (stp + BitVec.ofNat 32 24), memLoad32 _ (stp + BitVec.ofNat 32 28)] = _
    unfold kcSetupMem
    simp (disch := decide) only [ls_sep S.stF.symm]
    rw [stL 0 (by decide), stL 4 (by decide), stL 8 (by decide), stL 12 (by decide), stL 16 (by decide),
      stL 20 (by decide), stL 24 (by decide), stL 28 (by decide)]
    rfl
  · intro x h1 _
    rw [← hMs]; unfold kcSetupMem
    simp (disch := decide) only [st_get_sep h1]
    exact frSv x h1
  · intro q hq
    have h3 : kcSetupKeep q = true := by revert q; decide
    exact k3 q h3 (fun e => by subst e; exact absurd hq (by decide))
  · intro r o h
    rw [← hMs]; unfold kcSetupMem
    simp only [kcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp (disch := decide) only [ls_lit]
      rw [← hMsv]; simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]

theorem beq_refl_w (a : Word) : branchTaken .beq a a = true := by
  unfold branchTaken; exact decide_eq_true rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The exit, from 0x54 after the last block: restore the saved registers,
pop the frame, and return. -/
theorem kc_epi {P F stp bp : Word} {n : Nat} {M0 Ms M : Word → BitVec 8} {g : Fin 32 → Word} {hv : Sha256.V8}
    {m : Machine} (S : KCOS P F stp bp n M0) (O : KCO P F stp bp n M0 Ms g n hv M m)
    (hsl : ∀ r o, (r, o) ∈ kcPs → memLoad32 Ms (F + o) = g r) :
    ∃ m', Steps m m' ∧ m'.pc = g ra &&& ~~~1 ∧ m'.mem = M ∧ reg m' sp = F + 0xE0 ∧
      (∀ r o, (r, o) ∈ kcPs → reg m' r = g r) ∧ ∀ q, kcKeep q = true → reg m' q = g q := by
  have hc0 := S.cIn O.fr S.code S.sC S.stC (Nat.le_refl _)
  obtain ⟨m1, d1, u1⟩ := O.st.lw hc0 kc_at_54 (off' := 0x56) (by decide)
    (by rw [O.rsp]; exact fr_al S.hF (by decide))
  rw [O.rsp, O.m8] at u1
  obtain ⟨m2, d2, u2⟩ := u1.taken hc0 0x22E kc_at_56 (by decide)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [O.r9]; exact beq_refl_w _)
  have sp2 : upd (reg m) a0 (bp + BitVec.ofNat 32 (64 * n)) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; exact O.rsp
  obtain ⟨m3, c3, u3⟩ := St.block (restoreBlock kcPs) u2 hc0 kcRestore_end
    (restoreBlock_ok M F kcPs _ sp2 kcPs_sp fun p hp => fr_al' S.hF (kcPs_range p hp).1)
  simp only [restoreBlock_run M F kcPs _ sp2 kcPs_sp] at u3
  have rsp3 : restoreRegs M F (upd (reg m) a0 (bp + BitVec.ofNat 32 (64 * n))) kcPs sp = F := by
    rw [restoreRegs_sp _ _ _ _ kcPs_sp]; exact sp2
  obtain ⟨m4, d4, u4⟩ := u3.aluImm hc0 kc_at_248 (off' := 0x24A) (by decide)
  obtain ⟨m5, d5, pc5, mem5, regs5⟩ := u4.jalr hc0 kc_at_24a
  have slot : ∀ r o, (r, o) ∈ kcPs → memLoad32 M (F + o) = g r := fun r o h => by
    rw [← hsl r o h]
    obtain ⟨_, h1, h2⟩ := kcPs_range (r, o) h
    dsimp only at h1 h2
    refine memLoad32_congr fun j hj => O.sv _ ?_ ?_
    · rw [← ofNat_toNat_self o, add_ofNat_assoc]
      have := sep_offsets F (c := 0) (n := 0xAC) (d := o.toNat + j) (k := 1) (.inl (by omega)) (by decide)
        (by omega)
      rwa [add_ofNat_zero] at this
    · rw [← ofNat_toNat_self o, add_ofNat_assoc]; exact S.stF.subR (by omega)
  refine ⟨m5, .cons d1 (.cons d2 (c3.trans (.cons d4 (.cons d5 (.refl _))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc5]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, slot ra 0xDC (by decide)]
  · rw [mem5]
  · rw [regs5]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp3]
  · intro r o h
    rw [regs5]
    simp only [kcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slot _ _ (by decide)
  · intro q hq
    rw [regs5, upd_kp hq rfl rfl]
    simp only [restoreRegs]
    rw [upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl,
      upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl,
      upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, upd_kp hq rfl rfl, O.keep q hq]

theorem kcEnv_static {M : Word → BitVec 8} {P sp0 stp bp : Word} {n : Nat} (env : KCEnv M P sp0 stp bp n) :
    KCOS P (sp0 + 0xFFFFFF20) stp bp n M := by
  have hS := env.hS
  have hFw : (sp0 + 0xFFFFFF20).toNat + 0xE0 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (0xFFFFFF20 : Word).toNat = 0xFFFFFF20 from rfl]
    have := sp0.isLt
    omega
  exact ⟨env.hP, aligned_add env.hsp (k := 0xFFFFFF20) (by decide), hFw, env.hstp, env.hwbp, env.code, env.idx,
    env.stub, env.body, env.kdata, env.sC, env.sI, env.sU, env.sB, env.sK, env.stC, env.stI, env.stU, env.stB,
    env.stK, env.stF, env.bF, env.bSt⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `sha2::sha256::compress256`, compact backend**, called with
the state at `stp` and `n` 64-byte blocks at `bp`. It stores the state that
SHA-256's compression function computes from the eight words at `stp` and the
`n` blocks, returns with `sp` and every register but `t0` through `t6` and
`a0` through `a7` as they were, and changes no memory outside the 0xE0 bytes
of stack below `sp` and the state. -/
theorem kcCompress_correct (m : Machine) {P sp0 stp bp retAddr : Word} {n : Nat}
    (env : KCEnv m.mem P sp0 stp bp n) (hpc : m.pc = P)
    (ha0 : reg m a0 = stp) (ha1 : reg m a1 = bp) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 →
        q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) →
        q ≠ (31 : Fin 32) → reg m' q = reg m q) ∧
      wordsAt m'.mem stp 8 = (blockList m.mem bp n).foldl Sha256.compress (wordsAt m.mem stp 8) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep stp 32 x 1 → m'.mem x = m.mem x := by
  have S := kcEnv_static env
  have hn : n < 2 ^ 26 := by have := env.hwbp; omega
  obtain ⟨m1, Ms, c1, O0, hsl⟩ := kc_pro m S hn hpc ha0 ha1 ha2 hsp
  obtain ⟨m2, M2, c2, On⟩ := kc_outer S n 0 Ms m1 (Nat.zero_add n) O0
  obtain ⟨m3, c3, pc3, mem3, sp3, regs3, keep3⟩ := kc_epi S On hsl
  refine ⟨m3, c1.trans (c2.trans c3), by rw [pc3, hra, hret], ?_, ?_, ?_, ?_⟩
  · rw [sp3, BitVec.add_assoc]; exact BitVec.add_zero _
  · intro q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31
    have cat := (by decide : ∀ q : Fin 32, q = 0 ∨ q = sp ∨ q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
      q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨
      q = (23 : Fin 32) ∨ q = (24 : Fin 32) ∨ q = (25 : Fin 32) ∨ q = (26 : Fin 32) ∨ q = (27 : Fin 32) ∨
      kcKeep q = true ∨ q = (5 : Fin 32) ∨ q = (6 : Fin 32) ∨ q = (7 : Fin 32) ∨ q = a0 ∨ q = a1 ∨ q = a2 ∨
      q = a3 ∨ q = a4 ∨ q = a5 ∨ q = a6 ∨ q = a7 ∨ q = (28 : Fin 32) ∨ q = (29 : Fin 32) ∨
      q = (30 : Fin 32) ∨ q = (31 : Fin 32)) q
    rcases cat with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h
    · subst h; rfl
    · subst h; rw [sp3, hsp, BitVec.add_assoc]; exact BitVec.add_zero _
    · subst h; exact regs3 _ 0xDC (by decide)
    · subst h; exact regs3 _ 0xD8 (by decide)
    · subst h; exact regs3 _ 0xD4 (by decide)
    · subst h; exact regs3 _ 0xD0 (by decide)
    · subst h; exact regs3 _ 0xCC (by decide)
    · subst h; exact regs3 _ 0xC8 (by decide)
    · subst h; exact regs3 _ 0xC4 (by decide)
    · subst h; exact regs3 _ 0xC0 (by decide)
    · subst h; exact regs3 _ 0xBC (by decide)
    · subst h; exact regs3 _ 0xB8 (by decide)
    · subst h; exact regs3 _ 0xB4 (by decide)
    · subst h; exact regs3 _ 0xB0 (by decide)
    · subst h; exact regs3 _ 0xAC (by decide)
    · exact keep3 q h
    · exact absurd h q5
    · exact absurd h q6
    · exact absurd h q7
    · exact absurd h q10
    · exact absurd h q11
    · exact absurd h q12
    · exact absurd h q13
    · exact absurd h q14
    · exact absurd h q15
    · exact absurd h q16
    · exact absurd h q17
    · exact absurd h q28
    · exact absurd h q29
    · exact absurd h q30
    · exact absurd h q31
  · rw [mem3, On.hst, kcState_toList]
  · intro x h1 h2; rw [mem3]; exact On.fr x h1 h2

end C3.RV32
