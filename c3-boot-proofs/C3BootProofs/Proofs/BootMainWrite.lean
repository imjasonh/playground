import C3BootProofs.Proofs.BootMainPick
import C3BootProofs.Proofs.BootMainRecord

/-!
# `boot_main`'s calls to `write_state`

`boot_main` calls its second closure, `write_state`, with the copy to
replace and an 8-byte state in its frame. `bmw_call` runs one such call
with `bootWrite_correct`: when the state there is the record that
`decideBoot` writes, the ROM's write gets exactly that record, which is what
`BmHyp` requires of it.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-- The state at `st` is one `write_state` can encode: a slot number in the
preferred-slot byte, confirmed bits below 4, and either no trial (2) or a
trial slot with at most 3 boots left. -/
def BmwValid (M : Word → BitVec 8) (st : Word) : Prop :=
  (M (st + 7)).toNat ≤ 1 ∧ (M (st + 6)).toNat ≤ 3 ∧
    ((M (st + 4)).toNat ≤ 1 ∧ (M (st + 5)).toNat ≤ 3 ∨ M (st + 4) = 2)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- A call at `off` from `boot_main` to `write_state(copy, F + j)`, where
`copy` is the copy that `bootstate::read` returned and the state at `F + j`
is the record that `decideBoot` writes. It returns to `off + 8`
with the registers in `romKeep` and the memory outside its stack as they
were. -/
theorem bmw_call {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} {off j : Nat} {imm o : Word} {w : State}
    (s : St n.mem BM n off (reg n)) (hsp : reg n sp = F) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hj : j + 8 ≤ 0xBE80) (hj4 : j % 4 = 0) (ha0 : reg n a0 = bmCopy (bmRecs flash).2) (ha1 : reg n a1 = F + BitVec.ofNat 32 j)
    (hW : (bmDecision flash pinned policy M0).write = some w)
    (hst : bmrSt n.mem (F + BitVec.ofNat 32 j) = w) (hv : BmwValid n.mem (F + BitVec.ofNat 32 j))
    (h1 : fetchRel bootMainCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BM + BitVec.ofNat 32 off + imm + o = BW)
    (he8 : (BM + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem BM n' (off + 8) (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      BmKeep M0 n'.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) ∧
      ∀ x, Sep (F - BitVec.ofNat 32 (0x90 + romStack)) (0x90 + romStack) x 1 → n'.mem x = n.mem x := by
  have C := X.env
  have hlo := C.hlo; have hhi := C.hhi; have h16 := C.hsp; have hrs := C.hrs; have hrs4 := C.hrs4
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  rw [hKv] at hlo; rw [hbp] at hhi
  have hiM : ∀ x : Word, 0x40000000 ≤ x.toNat → n.mem x = M0 x := hK.hiOf C
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := BW) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg n1 sp = F := by rw [r1 _ (by decide), hsp]
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [mem1]; exact hK
  have BW1 : BWCode n1.mem :=
    { self := hK1.codeIn C C.bw.self (.inr ⟨by decide, by decide⟩)
      memset := hK1.codeIn C C.bw.memset (.inr ⟨by decide, by decide⟩)
      copy := hK1.codeIn C C.bw.copy (.inr ⟨by decide, by decide⟩)
      stub := hK1.codeIn C C.bw.stub (.inr ⟨by decide, by decide⟩)
      body := hK1.codeIn C C.bw.body (.inr ⟨by decide, by decide⟩)
      crc := hK1.codeIn C C.bw.crc (.inr ⟨by decide, by decide⟩)
      magic := hK1.codeIn C C.bw.magic (.inl (by decide))
      version := hK1.codeIn C C.bw.version (.inl (by decide)) }
  have hS : (F - BitVec.ofNat 32 (0x90 + romStack)).toNat = F.toNat - (0x90 + romStack) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 0x90 + romStack) (by omega)]; omega
  have hst8 : (F + BitVec.ofNat 32 j).toNat = F.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hv7, hv6, hv45⟩ := hv
  have hmag : Sep (F - BitVec.ofNat 32 (0x90 + romStack)) (0x90 + romStack) (BitVec.ofNat 32 bsMagicAddress) 4 :=
    (sep_of_le (by rw [hS, show (BitVec.ofNat 32 bsMagicAddress).toNat = 0x3fcc475e from rfl]; omega)
      (by rw [hS]; omega)).symm
  have hver : Sep (F - BitVec.ofNat 32 (0x90 + romStack)) (0x90 + romStack) (BitVec.ofNat 32 bsVersionAddress) 2 :=
    (sep_of_le (by rw [hS, show (BitVec.ofNat 32 bsVersionAddress).toNat = 0x3fcc46b6 from rfl]; omega)
      (by rw [hS]; omega)).symm
  obtain ⟨n2, c2, pc2, keep2, mem2⟩ := bootWrite_correct n1 (copy := bmCopy (bmRecs flash).2)
    (st := F + BitVec.ofNat 32 j) BW1 (C.rom.hi (hK1.hiOf C) C.hrb (by have := C.hrl; omega)) C.hrb
    (by have := C.hrl; omega) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    (by rw [regs1]; simp +decide only [upd, ↓reduceIte]) (even_clear _ he8)
    (by rw [sp1]; omega) hrs hrs4 (by rw [sp1]; omega) (by rw [sp1]; omega)
    (by rw [sp1]; exact hmag) (by rw [sp1]; exact hver)
    (by rw [sp1]; exact (sep_of_le (by rw [hS, hst8]; omega) (by rw [hst8]; omega)).symm)
    (by rw [hst8]; omega)
    X.unlock
    (fun mm hcm hpm hpre hsm => X.erase mm hcm hpm hpre hsm)
    (fun mm hcm hpm ⟨e0, e2, e3⟩ hsm => X.write mm hcm hpm ⟨e0, e2, w, hW, by
      rw [List.map_congr_left (g := fun i => (bwRec n1.mem (F + BitVec.ofNat 32 j) i).toNat)
        fun i hi => by rw [e3 i (List.mem_range.mp hi)]]
      rw [mem1] at ⊢
      rw [bmr_enc n.mem _ hv7 hv6 hv45, hst]⟩ hsm)
    X.log
  rw [sp1] at mem2
  refine ⟨n2, c1.trans c2, ⟨?_, rfl, fun _ => rfl⟩, fun q hq => ?_, hK.step fun x hx => ?_,
    fun x hx => by rw [mem2 x hx, mem1]⟩
  · rw [pc2]
  · rw [keep2 q hq, regs1]; exact updz s.zero (by rintro rfl; exact absurd hq (by decide))
  · have hW' : (top - BitVec.ofNat 32 (bmK R romStack stack0)).toNat = top.toNat - bmK R romStack stack0 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
    rw [mem2 x (bmt_sep_in hx (by rw [hS, hW', hKv]; omega) (by rw [hS, hW', hKv]; omega)), mem1]

set_option maxRecDepth 100000 in
theorem bmc_c0_range : 0x40000000 ≤ (BitVec.ofNat 32 bootMainClosure0Address).toNat ∧
    (BitVec.ofNat 32 bootMainClosure0Address).toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide

theorem bmc_level_le : ∀ f : Fuses, level f ≤ f.length
  | [] => Nat.le_refl 0
  | b :: f => by
    have := bmc_level_le f
    cases b <;> simp only [level, List.length_cons, ite_true, ite_false, Bool.false_eq_true] <;> omega

theorem bmc_pop_lt (w : Word) : (btPop w).toNat < 256 := by
  rw [BootLevel.btPop_level]
  have := bmc_level_le (Fuses.ofNat ((w.toNat >>> 14) % 65536))
  have hl : (Fuses.ofNat ((w.toNat >>> 14) % 65536)).length = 16 := by
    simp only [Fuses.ofNat, List.length_map, List.length_range, maxLevel]
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- A call at `off` from `boot_main` to its first closure with the result
at `F + k`, the `Buffers` at `F + 0x50`, slot `sl`, and the entry level: it
returns to `off + 8` with the registers in `romKeep` kept and memory
outside its stack, the result, and the `Buffers` as it was, and the result
says what `bmcAccept` says, or it panics. -/
theorem bmc_call {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} {off k : Nat} {imm o : Word} {sl : Slot}
    (s : St n.mem BM n off (reg n)) (hsp : reg n sp = F) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hk1 : 0xB9A4 ≤ k) (hk2 : k + 0x12C ≤ 0xBE80) (hk4 : k % 4 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 k) (ha1 : reg n a1 = btPop (memLoad32 M0 efuseRd))
    (ha2 : reg n a2 = F + BitVec.ofNat 32 0x50) (ha3 : reg n a3 = BitVec.ofNat 32 (bmSlotNum sl))
    (h1 : fetchRel bootMainCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BM + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 bootMainClosure0Address)
    (he8 : (BM + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) :
    (∃ n', Steps n n' ∧ St n'.mem BM n' (off + 8) (reg n') ∧ (∀ q, romKeep q = true → reg n' q = reg n q) ∧
      BmKeep M0 n'.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) ∧
      (∀ x, Sep (F - BitVec.ofNat 32 stack0) stack0 x 1 → Sep (F + BitVec.ofNat 32 k) 0x12C x 1 →
        Sep (F + BitVec.ofNat 32 0x50) 0xB954 x 1 → n'.mem x = n.mem x) ∧
      match bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum sl)) with
      | none => n'.mem (F + BitVec.ofNat 32 k + 0xC) = 0xFF
      | some (mf, sv, _) =>
        n'.mem (F + BitVec.ofNat 32 k + 0xC) ≠ 0xFF ∧ n'.mem (F + BitVec.ofNat 32 k + 0x128) = BitVec.ofNat 8 sv ∧
          memLoad32 n'.mem (F + BitVec.ofNat 32 k + 0x120) =
            BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum sl)) + mf.image.offset) ∧
          AccOk flash (BitVec.ofNat 32 (bmSlotNum sl)) mf n'.mem (F + BitVec.ofNat 32 k)) ∨
    Panics n := by
  have C := X.env
  have hlo := C.hlo; have hhi := C.hhi
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  rw [hKv] at hlo; rw [hbp] at hhi
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ :=
    s.callRa (cb := BitVec.ofNat 32 bootMainClosure0Address) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg n1 sp = F := by rw [r1 _ (by decide), hsp]
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [mem1]; exact hK
  have eF : ∀ c : Nat, c ≤ 0xBE80 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hS : (F - BitVec.ofNat 32 stack0).toNat = F.toNat - stack0 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := stack0) (by omega)]; omega
  have hsl : bmcAccept flash pinned policy (BitVec.toNat (btPop (memLoad32 M0 efuseRd)))
      (BitVec.ofNat 32 (bmSlotNum sl)) = bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum sl)) :=
    rfl
  rcases X.c0 X.rom n1 (F + BitVec.ofNat 32 k) (F + BitVec.ofNat 32 0x50) (BitVec.ofNat 32 (bmSlotNum sl))
      (btPop (memLoad32 M0 efuseRd)) (hK1.codeIn C C.c0 (.inr bmc_c0_range)) (X.hE _ hK1) pc1
      (by rw [sp1]; omega) (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
      (by rw [r1 _ (by decide), ha2]) (by rw [r1 _ (by decide), ha3]) (by cases sl <;> decide)
      ⟨by rw [sp1]; have := X.env.hsp; omega, by rw [sp1]; omega, by rw [sp1]; omega,
        by rw [eF k (by omega)]; have := X.env.hsp; omega, by rw [eF k (by omega)]; omega,
        by rw [eF k (by omega)]; omega, by rw [eF 0x50 (by decide)]; have := X.env.hsp; omega,
        by rw [sp1, eF 0x50 (by decide)]; omega, by rw [eF 0x50 (by decide)]; omega, bmc_pop_lt _,
        by rw [show reg n1 ra = BM + BitVec.ofNat 32 (off + 8) by rw [regs1]; simp +decide only [upd, ↓reduceIte]]
           exact even_clear _ he8⟩
      (sep_of_le (by rw [eF 0x50 (by decide), eF k (by omega)]; omega) (by rw [eF k (by omega)]; omega)).symm
      (by rw [sp1]; exact (sep_of_le (by rw [hS, eF k (by omega)]; omega) (by rw [eF k (by omega)]; omega)).symm)
      (by rw [sp1]; exact (sep_of_le (by rw [hS, eF 0x50 (by decide)]; omega) (by rw [eF 0x50 (by decide)]; omega)).symm)
    with ⟨n2, c2, pc2, keep2, mem2, res2⟩ | hp
  · rw [sp1] at mem2
    refine .inl ⟨n2, c1.trans c2, ⟨?_, rfl, fun _ => rfl⟩, fun q hq => ?_, hK.step fun x hx => ?_,
      fun x h1 h2 h3 => by rw [mem2 x h1 h2 h3, mem1], ?_⟩
    · rw [pc2, regs1]; simp +decide only [upd, ↓reduceIte]; exact even_clear _ he8
    · rw [keep2 q hq, regs1]; exact updz s.zero (by rintro rfl; exact absurd hq (by decide))
    · have hW' : (top - BitVec.ofNat 32 (bmK R romStack stack0)).toNat = top.toNat - bmK R romStack stack0 := by
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
      rw [mem2 x (bmt_sep_in hx (by rw [hS, hW', hKv]; omega) (by rw [hS, hW', hKv]; omega))
        (bmt_sep_in hx (by rw [eF k (by omega), hW', hKv]; omega) (by rw [eF k (by omega), hW', hKv]; omega))
        (bmt_sep_in hx (by rw [eF 0x50 (by decide), hW', hKv]; omega) (by rw [eF 0x50 (by decide), hW', hKv]; omega)),
        mem1]
    · rw [hsl] at res2; exact res2
  · exact .inr (Panics.of_steps c1 hp)

end C3.RV32.Cur
