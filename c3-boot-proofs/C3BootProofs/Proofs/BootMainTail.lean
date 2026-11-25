import C3BootProofs.Proofs.BootMainSpec
import C3BootProofs.Spec.Boot

/-!
# `boot_main`: what it assumes, what it ends in, and its last call

`BmHyp` collects what the proof of `boot_main` assumes: the code and stack
in `BmEnv`, the ROM's flash reads and routines, and the contract of the first
closure. `BmJump` is the end that the headline theorem states: a jump into
the slot that `decideBoot` boots, with `boot`'s memory. `bmt_tail` covers
`boot_main` from 0x348, where it copies the chosen `Accepted` bytes to the
argument of `boot` and calls `boot`.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-! ## The decision -/

/-- The eFuse level that `boot_main` reads at entry: the popcount of the
level field of the eFuse register. -/
def bmLevel (M0 : Word → BitVec 8) : Nat := (btPop (memLoad32 M0 efuseRd)).toNat

/-- The check that `boot_main`'s first closure makes of a slot: its
security version, when `acceptTufSlot` accepts it at the entry level. -/
def bmCheck (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (M0 : Word → BitVec 8)
    (sl : Slot) : Option Nat :=
  (bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum sl))).map (·.2.1)

/-- The decision that `boot_main` carries out: `decideBoot` on the records
in flash, the entry level, and `bmCheck`. -/
def bmDecision (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (M0 : Word → BitVec 8) :
    Decision :=
  decideBoot (bmRecs flash).1 (bmLevel M0) (bmCheck flash pinned policy M0)

/-! ## The assumptions and the end -/

/-- **What the proof of `boot_main` assumes**, for flash `flash`, entry
memory `M0`, and the stack pointer `top`: the code and stack (`BmEnv`), the
ROM's flash reads (`RomRead`), the ROM routines that `boot_main` and its
callees call, and the first closure's contract, whose memory condition `E`
holds of every memory that keeps `M0` outside `boot_main`'s stack.

The ROM's flash-write routine may only be entered with 32 bytes that decode
to the record that `bmDecision` writes, at the address of the copy that
`bootstate::read` didn't return, and the erase routine only with that
copy's sector. -/
structure BmHyp (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (M0 : Word → BitVec 8)
    (top : Word) (R romStack stack0 : Nat) (romBase : Word) (romCode : List Nat)
    (E : (Word → BitVec 8) → Prop) : Prop where
  env : BmEnv M0 top R romStack stack0 romBase romCode
  rom : RomRead flash R romBase romCode
  log : RomFn romBase romCode 0x40000040 romStack fun _ => True
  unlock : RomFn romBase romCode 0x40000140 romStack fun _ => True
  erase : RomFn romBase romCode 0x40000128 romStack fun n => reg n a0 = bwAddr (bmCopy (bmRecs flash).2) >>> 12
  write : RomFn romBase romCode 0x4000012C romStack fun n =>
    reg n a0 = bwAddr (bmCopy (bmRecs flash).2) ∧ reg n a2 = 32 ∧
      ∃ w, (bmDecision flash pinned policy M0).write = some w ∧
        decodeRecord ((List.range 32).map fun i => (n.mem (reg n a1 + BitVec.ofNat 32 i)).toNat) = some w
  suspend : RomFn romBase romCode 0x40000524 romStack fun _ => True
  invalidate : RomFn romBase romCode 0x400004D8 romStack fun _ => True
  resume : RomFn romBase romCode 0x40000528 romStack fun _ => True
  c0 : Closure0Contract flash R romBase romCode pinned policy stack0 E
  hE : ∀ M, BmKeep M0 M (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) → E M

/-- Where `boot_main` keeps the `Accepted` bytes that it passes to `boot`. -/
def bmAcc (top : Word) : Word := top - 0x3B0

/-- **The jump into the application.** The machine `m'` is at the entry
point of slot `slot`, which `bmDecision` boots at security level `target`:
`bmcAccept` accepts the slot, the image's header `h` decodes, `target` is at
most the entry level, `a0` holds the slot, and the memory outside the
`K`-byte stack below `top` and the peripheral registers is what `boot` loads
from memory `Mb`. `Mb` keeps `M0` outside that stack and holds `h` at
`bmAcc top`. -/
def BmJump (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (M0 : Word → BitVec 8) (top : Word)
    (K : Nat) (m' : Machine) : Prop :=
  ∃ (slot : Slot) (target : Nat) (mf : Manifest) (sv t : Nat) (h : ImageHeader) (Mb : Word → BitVec 8),
    (bmDecision flash pinned policy M0).outcome = .boot slot target ∧
    bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum slot)) = some (mf, sv, t) ∧
    decodeImageHeader (bmcImage flash (BitVec.ofNat 32 (bmSlotNum slot)) mf) mf.image.length = some h ∧
    target ≤ bmLevel M0 ∧
    m'.pc = BitVec.ofNat 32 h.entryPoint &&& ~~~1 ∧
    reg m' a0 = BitVec.ofNat 32 (bmSlotNum slot) ∧
    BmKeep M0 Mb (top - BitVec.ofNat 32 K) K ∧ HdrAt Mb (bmAcc top) h ∧
    ∀ x, Sep (top - BitVec.ofNat 32 K) K x 1 → (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat) →
      m'.mem x = bootMem flash Mb (bmAcc top)
        (BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset)) x

/-- From `n`, the machine reaches a state that `J` holds of, or panics. -/
def BmEnd (J : Machine → Prop) (n : Machine) : Prop := (∃ m', Steps n m' ∧ J m') ∨ Panics n

theorem BmEnd.pre {J : Machine → Prop} {n n' : Machine} (h : Steps n n') (e : BmEnd J n') : BmEnd J n := by
  rcases e with ⟨m', h', hj⟩ | hp
  · exact .inl ⟨m', h.trans h', hj⟩
  · exact .inr (Panics.of_steps h hp)

/-! ## Helpers -/

theorem bmt_load_congr {M M' : Word → BitVec 8} {b b' : Word}
    (h : ∀ j, j < 4 → M (b + BitVec.ofNat 32 j) = M' (b' + BitVec.ofNat 32 j)) :
    memLoad32 M b = memLoad32 M' b' := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at h0
  rw [h0, show b + 1 = b + BitVec.ofNat 32 1 from rfl, h 1 (by decide),
    show b + 2 = b + BitVec.ofNat 32 2 from rfl, h 2 (by decide),
    show b + 3 = b + BitVec.ofNat 32 3 from rfl, h 3 (by decide)]
  rfl

/-- `HdrAt` reads only the first 0x10C bytes, so it carries over to a copy. -/
theorem bmt_hdr_move {M M' : Word → BitVec 8} {b b' : Word} {h : ImageHeader} (hH : HdrAt M b h)
    (hl : h.segments.length ≤ 16)
    (hc : ∀ i, i < 0x10C → M' (b' + BitVec.ofNat 32 i) = M (b + BitVec.ofNat 32 i)) : HdrAt M' b' h := by
  have w : ∀ c, c + 4 ≤ 0x10C → memLoad32 M' (b' + BitVec.ofNat 32 c) = memLoad32 M (b + BitVec.ofNat 32 c) :=
    fun c hc4 => bmt_load_congr fun j hj => by rw [add_ofNat_assoc, add_ofNat_assoc]; exact hc _ (by omega)
  obtain ⟨h1, h2, h3⟩ := hH
  refine ⟨(w 0x100 (by decide)).trans h1, (w 0x108 (by decide)).trans h2, fun j hj => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h3 j hj
  exact ⟨(w _ (by omega)).trans a1, (w _ (by omega)).trans a2, (w _ (by omega)).trans a3,
    (hc _ (by omega)).trans a4⟩

theorem bmt_panicFns_lo : ∀ p ∈ panicFns, 0x40000000 ≤ p.1 := by decide

/-- The panic code survives changes to memory below 0x40000000. -/
theorem bmt_panic {M M' : Word → BitVec 8} (h : PanicCode M) (hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PanicCode M' := by
  intro p hp
  have h1 := bmt_panicFns_lo p hp
  have h2 := (panicFns_hi p hp).2
  have e : (BitVec.ofNat 32 p.1).toNat = p.1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact (h p hp).hi hx (by rw [e]; exact h1) (by rw [e]; omega)

/-- A range inside the `K` bytes at `W` is apart from what they are apart from. -/
theorem bmt_sep_in {W a x : Word} {K k : Nat} (h : Sep W K x 1) (ha : W.toNat ≤ a.toNat)
    (hk : a.toNat + k ≤ W.toNat + K) : Sep a k x 1 := by
  have e : a = W + BitVec.ofNat 32 (a.toNat - W.toNat) := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a.toNat - W.toNat) (by have := a.isLt; omega)]
    have := a.isLt; rw [Nat.mod_eq_of_lt (by omega)]; omega)
  rw [e]; exact h.sub (by omega)

theorem bmt_base4 (w : Word) (o : Nat) (ho : o % 4 = 0) : (bmcBase w + o) % 4 = 0 := by
  unfold bmcBase; split <;> omega

theorem bmt_base_lt (w : Word) : bmcBase w + 0x10000 < 2 ^ 32 := by
  unfold bmcBase; split <;> omega

theorem bmt_ult {a : Word} {t : Nat} (ht : t < 2 ^ 32) (h : a.ult (BitVec.ofNat 32 t) = false) : t ≤ a.toNat := by
  rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht] at h
  exact Nat.le_of_not_lt h

theorem bmt_lowbyte {t : Nat} (ht : t ≤ 16) : BitVec.ofNat 32 t &&& 0xFF = BitVec.ofNat 32 t := by
  have h : ∀ t, t < 17 → BitVec.ofNat 32 t &&& 0xFF = BitVec.ofNat 32 t := by decide
  exact h t (by omega)

theorem bmt_ult_eq (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).ult (BitVec.ofNat 32 b) = decide (a < b) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- The level that `boot_main` computes for `boot`: the larger of the entry
level and, for a confirmed slot, the slot's security version. -/
theorem bmt_burn (sv L : Nat) (cf : Bool) (hsv : sv ≤ 16) (hL : L ≤ 16) :
    (if (if cf = true then BitVec.ofNat 32 sv else 0 : Word).ult (BitVec.ofNat 32 L) = true then
      BitVec.ofNat 32 L else (if cf = true then BitVec.ofNat 32 sv else 0 : Word)) =
      BitVec.ofNat 32 (burnTarget sv cf L) := by
  unfold burnTarget
  cases cf
  · simp only [Bool.false_eq_true, ite_false, Bool.false_and]
    rw [show (0 : Word) = BitVec.ofNat 32 0 from rfl, bmt_ult_eq 0 L (by omega) (by omega)]
    cases L with
    | zero => rfl
    | succ k => rfl
  · simp only [ite_true, Bool.true_and]
    rw [bmt_ult_eq sv L (by omega) (by omega)]
    rcases Nat.lt_or_ge sv L with h | h
    · simp only [show decide (sv < L) = true from decide_eq_true h,
        show decide (L < sv) = false from decide_eq_false (Nat.not_lt.mpr (Nat.le_of_lt h)), ↓reduceIte,
        Bool.false_eq_true]
    · rcases Nat.lt_or_ge L sv with h' | h'
      · simp only [show decide (sv < L) = false from decide_eq_false (Nat.not_lt.mpr h),
          show decide (L < sv) = true from decide_eq_true h', ↓reduceIte, Bool.false_eq_true]
      · simp only [show decide (sv < L) = false from decide_eq_false (Nat.not_lt.mpr h),
          show decide (L < sv) = false from decide_eq_false (Nat.not_lt.mpr h'), ↓reduceIte, Bool.false_eq_true]
        rw [Nat.le_antisymm h h']

/-- The mask that `boot_main` makes from the confirmed bits `c`: all ones
when the slot with bit `b` is confirmed, else zero. -/
theorem bmt_mask (c p b : Nat) (hc : c < 4) (hp : p ≤ 1) (hb : b = 1 ∨ b = 2) :
    aluEval .add (aluEval .sltu (aluEval .and (aluEval .and (BitVec.ofNat 32 (c + 256 * p))
      (BitVec.ofNat 32 b)) 0xFF) 1) 0xFFFFFFFF = if (c &&& b != 0) = true then 0xFFFFFFFF else 0 := by
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  have hp' : p = 0 ∨ p = 1 := by omega
  rcases hc' with rfl | rfl | rfl | rfl <;> rcases hp' with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem bmt_mask_and (m v : Word) (cf : Bool) (hm : m = if cf = true then 0xFFFFFFFF else 0) :
    aluEval .and m v = if cf = true then v else 0 := by
  subst hm; cases cf
  · exact BitVec.zero_and
  · show (0xFFFFFFFF : Word) &&& v = v
    rw [BitVec.and_comm]; exact and_ff32 v


/-- `AccOk` reads only the first 0x10C bytes, so it carries over to a copy. -/
theorem bmt_acc_move {flash : Nat → BitVec 8} {slot : Word} {mf : Manifest} {M M' : Word → BitVec 8}
    {b b' : Word} (hA : AccOk flash slot mf M b)
    (hc : ∀ i, i < 0x10C → M' (b' + BitVec.ofNat 32 i) = M (b + BitVec.ofNat 32 i)) : AccOk flash slot mf M' b' :=
  fun h hd => bmt_hdr_move (hA h hd) (bmc_decode hd).1 hc

/-- `boot_main`'s `max` at `off`: `bltu a0, s7` over `mv s3, a0`. -/
theorem bmt_max {n : Machine} {off : Nat} (s : St n.mem BM n off (reg n)) (hc : CodeIn n.mem BM bootMainCode)
    (h1 : fetchRel bootMainCode off = some (.branch .bltu a0 (23 : Fin 32) 0x6, 4))
    (h2 : fetchRel bootMainCode (off + 4) = some (.alu .add (19 : Fin 32) x0 a0, 2)) :
    ∃ n', Steps n n' ∧ St n'.mem BM n' (off + 6) (reg n') ∧ n'.mem = n.mem ∧
      reg n' 19 = (if (reg n a0).ult (reg n 23) = true then reg n 19 else reg n a0) ∧
      ∀ r, r ≠ 19 → reg n' r = reg n r := by
  cases hb : (reg n a0).ult (reg n 23)
  · obtain ⟨n1, e1, t1⟩ := s.notTaken hc (off + 4) h1 (ofNat_add_ofNat off 4) hb
    obtain ⟨n2, e2, t2⟩ := t1.alu hc h2 (off' := off + 6)
      (by rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, ofNat_add_ofNat])
    refine ⟨n2, .cons e1 (.single e2), ⟨t2.pc, rfl, fun _ => rfl⟩, t2.mem, ?_, fun r hr => ?_⟩
    · rw [t2.regs]; simp +decide only [upd, ↓reduceIte]
      rw [s.zero]; exact BitVec.zero_add _
    · rw [t2.regs, updz s.zero hr]
  · obtain ⟨n1, e1, t1⟩ := s.taken hc (off + 6) h1 (ofNat_add_ofNat off 6) hb
    exact ⟨n1, .single e1, ⟨t1.pc, rfl, fun _ => rfl⟩, t1.mem, by rw [t1.regs, ite_eq_left rfl],
      fun r _ => t1.regs r⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- A call at `off` to `memcpy(F + 0xB9AD, F + c, 0x120)`, with the frame
at `F`: it copies the bytes and keeps the registers in `romKeep`. -/
theorem bmt_copy {M0 : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode) {n : Machine} {F : Word}
    {off c : Nat} {imm o : Word} (s : St n.mem BM n off (reg n)) (hsp : reg n sp = F)
    (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hc1 : 0xBACD ≤ c) (hc2 : c + 0x120 ≤ 0xBE80)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 0xB9AD) (ha1 : reg n a1 = F + BitVec.ofNat 32 c)
    (ha2 : reg n a2 = BitVec.ofNat 32 0x120)
    (h1 : fetchRel bootMainCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BM + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memcpyStubAddress)
    (he8 : (BM + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem BM n' (off + 8) (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      BmKeep M0 n'.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) ∧
      (∀ i, i < 0x120 → n'.mem (F + BitVec.ofNat 32 0xB9AD + BitVec.ofNat 32 i) =
        n.mem (F + BitVec.ofNat 32 c + BitVec.ofNat 32 i)) ∧
      ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep (F + BitVec.ofNat 32 0xB9AD) 0x120 x 1 → n'.mem x = n.mem x := by
  have hlo := C.hlo; have hhi := C.hhi; have h16 := C.hsp
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  rw [hbp] at hhi
  have eF : ∀ c : Nat, c ≤ 0xBE80 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hiM : ∀ x : Word, 0x40000000 ≤ x.toNat → n.mem x = M0 x := hK.hiOf C
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := s.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc h1 h2 hb (by decide)
  have r2 := PEnv.reg1 regs2 s.zero
  have sp2 : reg n2 sp = F := by rw [r2 _ (by decide), hsp]
  have hFm : (F + 0xFFFFFFF0).toNat = F.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; rw [hKv] at hlo; omega
  have hst8 : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = (img% memcpyBodyAddress) := by decide
  have hiS : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M0 x := fun x hx => by rw [mem2]; exact hiM x hx
  rw [hKv] at hlo
  obtain ⟨n3, c3, pc3, sp3, _, f3, k3⟩ := memcpy_correct n2 (BitVec.ofNat 32 memcpyStubAddress)
    (BM + BitVec.ofNat 32 (off + 8)) (F + BitVec.ofNat 32 0xB9AD) (F + BitVec.ofNat 32 c) 0x120
    (fun i hi => (C.stub.hi hiS (by decide) (by decide)) i hi) (by decide) pc2
    (by rw [r2 _ (by decide), ha0]) (by rw [r2 _ (by decide), ha1]) (by rw [r2 _ (by decide), ha2])
    (by rw [regs2]; simp +decide [upd]) (even_clear _ he8)
    (by
      rw [sp2]
      exact { code := C.body.hi hiS (by rw [hst8]; decide) (by rw [hst8]; decide)
              hDC := sep_of_le (by rw [eF _ (by decide), hst8]; omega) (by rw [hst8]; decide)
              hFC := sep_of_le (by rw [hFm, hst8]; omega) (by rw [hst8]; decide)
              hdF := (sep_of_le (by rw [hFm, eF _ (by decide)]; omega) (by rw [eF _ (by decide)]; omega)).symm
              hsF := (sep_of_le (by rw [hFm, eF _ (by omega)]; omega) (by rw [eF _ (by omega)]; omega)).symm
              hsep := sep_of_le (by rw [eF _ (by decide), eF _ (by omega)]; omega)
                (by rw [eF _ (by omega)]; omega)
              hF := by rw [hFm]; omega
              hFw := by rw [hFm]; omega
              hdw := by rw [eF _ (by decide)]; omega
              hsw := by rw [eF _ (by omega)]; omega })
  rw [sp2] at f3 sp3
  have out3 : ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep (F + BitVec.ofNat 32 0xB9AD) 0x120 x 1 → n3.mem x = n.mem x :=
    fun x h1 h2 => by rw [f3 x h1, copyBytes_sep h2 (Nat.le_refl _), mem2]
  refine ⟨n3, c2.trans c3, ⟨by rw [pc3], rfl, fun _ => rfl⟩, fun q hq => ?_, hK.step fun x hx => ?_,
    fun i hi => ?_, out3⟩
  · by_cases hqs : q = sp
    · rw [hqs, sp3, hsp]
    · have hne : ∀ q : Fin 32, romKeep q = true → q ≠ sp → q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧
          q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧
          q ≠ (30 : Fin 32) ∧ q ≠ ra := by decide
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := hne q hq hqs
      rw [k3 q d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 hqs, r2 q d14]
  · have hW : (top - BitVec.ofNat 32 (bmK R romStack stack0)).toNat = top.toNat - bmK R romStack stack0 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
    exact out3 x (bmt_sep_in hx (by rw [hFm, hW, hKv]; omega) (by rw [hFm, hW, hKv]; omega))
      (bmt_sep_in hx (by rw [eF _ (by decide), hW, hKv]; omega) (by rw [eF _ (by decide), hW, hKv]; omega))
  · rw [f3 _ (by
      rw [add_ofNat_assoc]
      exact sep_of_le (by rw [hFm, eF _ (by omega)]; omega) (by rw [eF _ (by omega)]; omega)),
      cb_in hi (by decide), mem2]

/-! ## From 0x348 to the jump -/

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **`boot_main` from 0x348.** With the frame at `F`, the chosen slot's
`Accepted` bytes at `F + 0xB9AD`, the slot in `s1`, the target in `s3`, the image's flash address in `s2`, and the entry level
in `s7`, `boot_main` copies the bytes to `bmAcc top` and calls `boot`, which
jumps into the slot or panics. -/
theorem bmt_tail {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x348 (reg n)) (hsp : reg n sp = F)
    (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {slot : Slot} {target : Nat} {mf : Manifest} {sv t : Nat}
    (hD : (bmDecision flash pinned policy M0).outcome = .boot slot target)
    (hA : bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum slot)) = some (mf, sv, t))
    (hAcc : AccOk flash (BitVec.ofNat 32 (bmSlotNum slot)) mf n.mem (F + BitVec.ofNat 32 0xB9AD))
    (h9 : reg n 9 = BitVec.ofNat 32 (bmSlotNum slot))
    (h19 : reg n 19 = BitVec.ofNat 32 target) (htg : target ≤ 16)
    (h18 : reg n 18 = BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset))
    (h23 : reg n 23 = btPop (memLoad32 M0 efuseRd)) :
    BmEnd (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have hlo := C.hlo; have hhi := C.hhi; have h16 := C.hsp; have hR4 := C.hR
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  rw [hKv] at hlo; rw [hbp] at hhi
  obtain ⟨hoff, _, _, h, hd, _⟩ := bmc_accept hA
  obtain ⟨hl16, hok, _⟩ := bmc_decode hd
  have hH := hAcc h hd
  have eF : ∀ c : Nat, c ≤ 0xBE80 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hiM : ∀ x : Word, 0x40000000 ≤ x.toNat → n.mem x = M0 x := hK.hiOf C
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  -- the copy's arguments, to 0x35E
  obtain ⟨n1, c1, u1⟩ := s.block bmB36 hc bmB36_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB36 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0x35E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have a0_1 : reg n1 a0 = F + BitVec.ofNat 32 0xBAD0 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB36, upd, ↓reduceIte]; rw [hsp]; exact BitVec.add_comm _ _
  have a1_1 : reg n1 a1 = F + BitVec.ofNat 32 0xB9AD := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB36, upd, ↓reduceIte]; rw [hsp]; rfl
  have a2_1 : reg n1 a2 = BitVec.ofNat 32 0x120 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB36, upd, ↓reduceIte]
  have k1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n1 r = reg n r := fun r h0 h1 h2 => by
    rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [bmB36]; revert h0 h1 h2; revert r; decide)]
  -- `memcpy(acc, temp, 0x120)`, to 0x366
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := t1.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) (by rw [m1]; exact hc)
    bm_at_35e bm_at_362 (by decide) (by decide)
  have r2 := PEnv.reg1 regs2 t1.zero
  have sp2 : reg n2 sp = F := by rw [r2 _ (by decide), k1 _ (by decide) (by decide) (by decide), hsp]
  have hFm : (F + 0xFFFFFFF0).toNat = F.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
  have hst8 : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = (img% memcpyBodyAddress) := by decide
  have hiS : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M0 x := fun x hx => by rw [mem2, m1]; exact hiM x hx
  obtain ⟨n3, c3, pc3, sp3, _, f3, k3⟩ := memcpy_correct n2 (BitVec.ofNat 32 memcpyStubAddress)
    (BM + BitVec.ofNat 32 (0x35E + 8)) (F + BitVec.ofNat 32 0xBAD0) (F + BitVec.ofNat 32 0xB9AD) 0x120
    (fun i hi => (C.stub.hi hiS (by decide) (by decide)) i hi) (by decide) pc2
    (by rw [r2 _ (by decide), a0_1]) (by rw [r2 _ (by decide), a1_1]) (by rw [r2 _ (by decide), a2_1])
    (by rw [regs2]; simp +decide [upd]) (even_clear _ (by decide))
    (by
      rw [sp2]
      exact { code := C.body.hi hiS (by rw [hst8]; decide) (by rw [hst8]; decide)
              hDC := sep_of_le (by rw [eF _ (by decide), hst8]; omega) (by rw [hst8]; decide)
              hFC := sep_of_le (by rw [hFm, hst8]; omega) (by rw [hst8]; decide)
              hdF := (sep_of_le (by rw [hFm, eF _ (by decide)]; omega) (by rw [eF _ (by decide)]; omega)).symm
              hsF := (sep_of_le (by rw [hFm, eF _ (by decide)]; omega) (by rw [eF _ (by decide)]; omega)).symm
              hsep := (sep_of_le (by rw [eF _ (by decide), eF _ (by decide)]; omega)
                (by rw [eF _ (by decide)]; omega)).symm
              hF := by rw [hFm]; omega
              hFw := by rw [hFm]; omega
              hdw := by rw [eF _ (by decide)]; omega
              hsw := by rw [eF _ (by decide)]; omega })
  rw [sp2] at f3 sp3
  have t3 : St n3.mem BM n3 0x366 (reg n3) := ⟨by rw [pc3], rfl, fun _ => rfl⟩
  -- memory after the copy
  have out3 : ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep (F + BitVec.ofNat 32 0xBAD0) 0x120 x 1 → n3.mem x = n.mem x :=
    fun x h1 h2 => by rw [f3 x h1, copyBytes_sep h2 (Nat.le_refl _), mem2, m1]
  have loF : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (F + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hFm]; omega) (by have := x.isLt; omega)
  have loA : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (F + BitVec.ofNat 32 0xBAD0) 0x120 x 1 := fun x hx =>
    sep_of_le (by rw [eF _ (by decide)]; omega) (by have := x.isLt; omega)
  have hi3 : ∀ x : Word, 0x40000000 ≤ x.toNat → n3.mem x = M0 x := fun x hx => by
    rw [out3 x (loF x hx) (loA x hx), hiM x hx]
  have cp3 : ∀ i, i < 0x10C → n3.mem (F + BitVec.ofNat 32 0xBAD0 + BitVec.ofNat 32 i) =
      n.mem (F + BitVec.ofNat 32 0xB9AD + BitVec.ofNat 32 i) := fun i hi => by
    rw [f3 _ (by
      rw [add_ofNat_assoc]
      exact sep_of_le (by rw [hFm, eF _ (by omega)]; omega) (by rw [eF _ (by omega)]; omega)),
      cb_in (by omega) (by decide), mem2, m1]
  have hc3 : CodeIn n3.mem BM bootMainCode := C.code.hi hi3 (by decide) (by decide)
  have k3' : ∀ r, r = 9 ∨ r = 18 ∨ r = 19 ∨ r = 23 → reg n3 r = reg n r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl <;>
      (rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r2 _ (by decide),
        k1 _ (by decide) (by decide) (by decide)])
  -- `boot`'s arguments, to 0x37A
  obtain ⟨n4, c4, u4⟩ := t3.block bmB37 hc3 bmB37_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have r4 : ∀ r, reg n4 r = (runBlock bmB37 (n3.mem, reg n3)).2 r := fun r => by rw [u4.regs]
  have t4 : St n4.mem BM n4 0x37A (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have a0_4 : reg n4 a0 = BitVec.ofNat 32 (bmSlotNum slot) := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bmB37, upd, ↓reduceIte]
    rw [k3' 9 (.inl rfl), h9]; cases slot <;> rfl
  have a3_4 : reg n4 a3 = BitVec.ofNat 32 target := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bmB37, upd, ↓reduceIte]
    rw [k3' 19 (.inr (.inr (.inl rfl))), h19]; exact bmt_lowbyte htg
  have a1_4 : reg n4 a1 = F + BitVec.ofNat 32 0xBAD0 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bmB37, upd, ↓reduceIte]
    rw [sp3]; exact BitVec.add_comm _ _
  have a2_4 : reg n4 a2 = BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset) := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bmB37, upd, ↓reduceIte]
    rw [k3' 18 (.inr (.inl rfl)), h18]; exact BitVec.zero_add _
  have a4_4 : reg n4 a4 = btPop (memLoad32 M0 efuseRd) := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bmB37, upd, ↓reduceIte]
    rw [k3' 23 (.inr (.inr (.inr rfl))), h23]; exact BitVec.zero_add _
  have sp4 : reg n4 sp = F := by
    rw [r4, runBlock_reg _ _ _ sp t3.zero (by decide), sp3]
  -- the call to `boot`
  obtain ⟨n5, c5, pc5, mem5, regs5⟩ := t4.callRa (cb := BT) (by rw [m4]; exact hc3) bm_at_37a bm_at_37e
    (by decide) (by decide)
  have r5 := PEnv.reg1 regs5 t4.zero
  have sp5 : reg n5 sp = F := by rw [r5 _ (by decide), sp4]
  have hi5 : ∀ x : Word, 0x40000000 ≤ x.toNat → n5.mem x = M0 x := fun x hx => by rw [mem5, m4]; exact hi3 x hx
  have hAccE : F + BitVec.ofNat 32 0xBAD0 = bmAcc top := BitVec.eq_of_toNat_eq (by
    rw [eF _ (by decide), bmAcc, BitVec.toNat_sub, show (0x3B0 : Word).toNat = 0x3B0 from rfl]; omega)
  have hA5 : HdrAt n5.mem (F + BitVec.ofNat 32 0xBAD0) h := bmt_hdr_move hH hl16 fun i hi => by
    rw [mem5, m4]; exact cp3 i hi
  have hal : (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset) % 4 = 0 :=
    bmt_base4 _ _ (by rw [hoff])
  have hbl : bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset < 2 ^ 32 := by
    rw [hoff]; exact bmt_base_lt _
  have himg : (BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset)).toNat % 4 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbl]; exact hal
  obtain ⟨hcnt, hkind, hram⟩ := bmc_hdr hA5 hl16 hok himg
  have hbK : btK R romStack = 0x40 + 16 + R + romStack := rfl
  have hSb : (F - BitVec.ofNat 32 (btK R romStack)).toNat = F.toNat - btK R romStack := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hbK]; omega
  have BC : BtCtx n5.mem (reg n5 sp) (F + BitVec.ofNat 32 0xBAD0)
      (BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset)) R romStack romBase romCode := by
    rw [sp5]
    exact { code := C.bt.hi hi5 (by decide) (by decide)
            rfw := C.rfw.hi hi5 (by decide) (by decide)
            epr := C.epr.hi hi5 (by decide) (by decide)
            panic := bmt_panic C.panic hi5
            rom := C.rom.hi hi5 C.hrb (by have := C.hrl; omega)
            hrb := C.hrb
            hrl := C.hrl
            hsp := by omega
            hspl := by rw [hbK]; omega
            hsph := by unfold dramEnd; omega
            hR := hR4
            hacc := by rw [eF _ (by decide)]; omega
            haccl := by rw [eF _ (by decide)]; omega
            sAS := (sep_of_le (by rw [hSb, eF _ (by decide)]; omega) (by rw [eF _ (by decide)]; omega)).symm
            kind := hkind
            ram := fun j hj hk => by
              obtain ⟨d1, d2, d3⟩ := hram j hj hk
              exact ⟨d1, by omega, sep_of_le (by rw [eF _ (by decide)]; omega) (by rw [eF _ (by decide)]; omega),
                sep_of_le (by rw [hSb, hbK]; omega) (by rw [hSb]; omega), d3⟩ }
  rcases boot_correct (flash := flash) n5 BC X.rom pc5 (by rw [r5 _ (by decide), a0_4])
      (by rw [r5 _ (by decide), a1_4]) (by rw [r5 _ (by decide), a2_4]) (by rw [r5 _ (by decide), a3_4])
      (by rw [r5 _ (by decide), a4_4]) X.log X.suspend X.invalidate X.resume with
    ⟨m', c6, pc6, a06, lev6, mem6⟩ | hp
  · refine .inl ⟨m', c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), slot, target, mf, sv, t, h,
      n5.mem, hD, hA, hd, ?_, ?_, a06, ?_, ?_, ?_⟩
    · have ht : target < 2 ^ 32 := by omega
      have e5 : memLoad32 n5.mem efuseRd = memLoad32 M0 efuseRd :=
        bmt_load_congr fun j hj => hi5 _ (by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, show efuseRd.toNat = 0x6000883C from rfl]; omega)
      rw [e5] at lev6
      rcases lev6 with e | e <;> exact bmt_ult ht e
    · rw [pc6, hA5.1]
    · refine hK.step fun x hx => ?_
      rw [mem5, m4]
      exact out3 x (bmt_sep_in hx (by rw [hFm, BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega)
          (by rw [hFm, BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega))
        (bmt_sep_in hx (by rw [eF _ (by decide), BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega)
          (by rw [eF _ (by decide), BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega))
    · rw [← hAccE]; exact hA5
    · intro x hx hp
      rw [← hAccE]
      exact mem6 x (by
        rw [sp5]
        exact bmt_sep_in hx (by rw [hSb, BitVec.toNat_sub, BitVec.toNat_ofNat, hKv, hbK]; omega)
          (by rw [hSb, BitVec.toNat_sub, BitVec.toNat_ofNat, hKv, hbK]; omega)) hp
  · exact .inr (Panics.of_steps (c1.trans (c2.trans (c3.trans (c4.trans c5)))) hp)

end C3.RV32.Cur
