import C3BootProofs.Proofs.AcceptLib
import C3BootProofs.Proofs.FlashRead
import C3BootProofs.Spec.Accept

/-!
# `boot_main`'s first closure: the stages' interface

Each stage of the closure starts at an offset in a state that its
precondition describes and ends in one of three ways: it panics, it reaches
one of the closure's exits (`AcFail`), or it reaches the next stage's offset
in a state that its postcondition describes. `AcStage` says that, and every
stage keeps `AcInv`: `sp`, `gp`, `tp`, the prologue's saves, and every byte
outside the closure's stack and `Buffers`.

`AcceptLib` turns each way into an exit into the closure's `None` return:
`ac_fail` from 0x166, `ac_none` from 0x16A, `ac_reject` from 0x7D6, and
`ac_from806` after the one instruction at 0x802.

`AcReadStage` is the first stage, from the prologue's end at 0x32 to 0x1AA:
the manifest, the image header, the image's SHA-256, and the bundle.

The last stage calls `sigstore::verify`, which writes up to 0x1A0 bytes
below the frame, so it keeps `AcInvW`, which keeps memory outside the 0x5C10
bytes from `B + 0xFFFFFE60`. `AcInv.wide` turns `AcInv` into `AcInvW`, and
`ac_exit_wide` is `ac_exit` from `AcInvW`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

/-- `sp + k`, with the frame at `B + 0x3A50`. -/
abbrev acSlot (B : Word) (k : Nat) : Word := B + BitVec.ofNat 32 (0x3A50 + k)

/-- The size of `Buffers`: the bundle, `doc`, `keys`, and the header. -/
abbrev acBufLen : Nat := 0xB954

/-- What every stage keeps. `M0` is memory when the closure was called. -/
structure AcInv (B Bf g t : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (n : Machine) : Prop where
  sp : reg n sp = B + 0x3A50
  gp : reg n (3 : Fin 32) = g
  tp : reg n (4 : Fin 32) = t
  saves : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k
  out : ∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → n.mem x = M0 x

/-- The ways into the closure's exits, for the result pointer `r`. At 0x166
and 0x7D6 the result is at `sp + 0x40`, and at 0x16A and 0x802 it is in
`s3`. At 0x7D6 and 0x802 the low byte of `s5` is the code to log. -/
def AcFail (B r : Word) (n : Machine) : Prop :=
  (n.pc = AC + 0x166 ∧ memLoad32 n.mem (acSlot B 0x40) = r) ∨
  (n.pc = AC + 0x16A ∧ reg n (19 : Fin 32) = r) ∨
  (n.pc = AC + 0x7D6 ∧ memLoad32 n.mem (acSlot B 0x40) = r ∧ (reg n (21 : Fin 32) &&& 0xFF).toNat < 0x27) ∨
  (n.pc = AC + 0x802 ∧ reg n (19 : Fin 32) = r)

/-- From `n0`, the closure panics, reaches an exit, or reaches offset `o'`
in a state that `Q` holds of. -/
def AcStage (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (n0 : Machine) (o' : Nat)
    (Q : Machine → Prop) : Prop :=
  ∃ n', Steps n0 n' ∧ (Halting n' ∨
    (AcInv B Bf g t v M0 n' ∧ (AcFail B r n' ∨ (n'.pc = AC + BitVec.ofNat 32 o' ∧ Q n'))))

/-- The flash address of slot `slot`'s first byte. -/
def acBase (slot : Word) : Nat := if slot = 0 then 0x30000 else 0x210000

/-- `len` bytes of flash from `a`. -/
def flashBytes (flash : Nat → BitVec 8) (a len : Nat) : Bytes :=
  (List.range len).map fun i => (flash (a + i)).toNat

/-- At 0x1AA: the slot's manifest is `mf`, the header buffer holds the
image's first `min length 0x114` bytes, the bundle buffer holds the bundle,
`sp + 0xD4` holds the image's SHA-256, and the registers and frame slots that
the next stages read hold the parts' addresses and lengths. -/
def AcReadPost (flash : Nat → BitVec 8) (B Bf r slot level : Word) (mf : Manifest) (n : Machine) : Prop :=
  memLoad32 n.mem (acSlot B 0x34) = Bf ∧
  memLoad32 n.mem (acSlot B 0x38) = BitVec.ofNat 32 mf.bundle.length ∧
  memLoad32 n.mem (acSlot B 0x3C) = slot ∧
  memLoad32 n.mem (acSlot B 0x40) = r ∧
  memLoad32 n.mem (acSlot B 0x44) = BitVec.ofNat 32 (acBase slot + mf.image.offset) ∧
  reg n (8 : Fin 32) = BitVec.ofNat 32 mf.bundle.length ∧
  reg n (9 : Fin 32) = BitVec.ofNat 32 mf.tuf.length ∧
  reg n (20 : Fin 32) = Bf + 0x4000 ∧
  reg n (22 : Fin 32) = BitVec.ofNat 32 (min mf.image.length 0x114) ∧
  reg n (24 : Fin 32) = BitVec.ofNat 32 (acBase slot + mf.tuf.offset) ∧
  reg n (25 : Fin 32) = Bf + 0xB840 ∧
  reg n (26 : Fin 32) = level ∧
  reg n (27 : Fin 32) = BitVec.ofNat 32 mf.image.length ∧
  acBase slot + mf.tuf.offset < 2 ^ 32 ∧
  memBytes n.mem (Bf + 0xB840) (min mf.image.length 0x114) =
    flashBytes flash (acBase slot + mf.image.offset) (min mf.image.length 0x114) ∧
  memBytes n.mem Bf mf.bundle.length = flashBytes flash (acBase slot + mf.bundle.offset) mf.bundle.length ∧
  memBytes n.mem (acSlot B 0xD4) 32 = sha256 (flashBytes flash (acBase slot + mf.image.offset) mf.image.length)

/-- **The read stage**, from 0x32 to 0x1AA, for the callees' code and data
`E` in memory that agrees with `M0` outside the stack and `Buffers`. It
reaches 0x1AA only when the manifest decodes, and then `AcReadPost` holds. -/
def AcReadStage (E : (Word → BitVec 8) → Prop) : Prop :=
  ∀ (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat), RomRead flash R romBase romCode →
  ∀ (n : Machine) (B Bf g t r slot level : Word) (v : Nat → Word) (M0 : Word → BitVec 8),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → E M) →
    CodeIn n.mem AC bootMainClosure0Code → Fr B 0x5A70 → Sep B 0x5A70 Bf acBufLen →
    Bf.toNat % 4 = 0 → Bf.toNat + acBufLen ≤ 0x40000000 → R ≤ 0x3A50 - 0x150 →
    St n.mem AC n 0x32 (reg n) → AcInv B Bf g t v M0 n →
    reg n (19 : Fin 32) = r → reg n (26 : Fin 32) = level → reg n (21 : Fin 32) = Bf →
    reg n (8 : Fin 32) = slot → reg n a3 = slot → reg n (24 : Fin 32) = 0x210000 →
    AcStage B Bf g t r v M0 n 0x1AA fun n' =>
      ∃ mf, decodeManifest (flashBytes flash (acBase slot) 32) = some mf ∧ AcReadPost flash B Bf r slot level mf n'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Every way into an exit returns `None`.** -/
theorem ac_exit {romBase : Word} {romCode : List Nat} {romStack : Nat}
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    {n : Machine} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
    (C : CodeIn n.mem AC bootMainClosure0Code) (CR : CodeIn n.mem romBase romCode)
    (T : CodeIn n.mem (BitVec.ofNat 32 acRejectTableAddress) acRejectTableData)
    (sRB : Sep B 0x5A70 romBase romCode.length) (F : Fr B 0x5A70) (hret : v 0 &&& ~~~1 = v 0)
    (sRC : Sep (r + 0xC) 1 AC bootMainClosure0Code.length) (sRS : Sep (r + 0xC) 1 B 0x5A70)
    (I : AcInv B Bf g t v M0 n) (h : AcFail B r n) :
    AcRet B v n (AcNone B r n.mem) := by
  have rsp : reg n sp = B + 0x3A50 := I.sp
  rcases h with ⟨hp, hr⟩ | ⟨hp, hr⟩ | ⟨hp, hr, hc⟩ | ⟨hp, hr⟩
  · exact ac_fail log hrs C CR F ⟨hp, rfl, fun _ => rfl⟩ rsp I.saves hret hr sRC sRS
  · subst hr
    exact ac_none log hrs C CR F ⟨hp, rfl, fun _ => rfl⟩ rsp I.saves hret sRC sRS
  · exact ac_reject log hrs C CR T sRB F ⟨hp, rfl, fun _ => rfl⟩ rsp I.saves hret hc hr sRC sRS
  · have s : St n.mem AC n 0x802 (reg n) := ⟨hp, rfl, fun _ => rfl⟩
    have hz := s.zero
    obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x806) acJ3 C (by decide) ⟨trivial, trivial⟩
    have M1 : n1.mem = n.mem := u1.mem
    have q : ∀ q : Fin 32, q.val ≠ 11 → reg n1 q = reg n q := fun q h0 => by
      rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acJ3]; revert h0; revert q; decide)]
    have q19 : reg n1 (19 : Fin 32) = r := by rw [q 19 (by decide), hr]
    have h := ac_from806 log hrs (by rw [M1]; exact C) (by rw [M1]; exact CR) sRB F ⟨u1.pc, rfl, fun _ => rfl⟩
      (by rw [q sp (by decide)]; exact rsp) (by rw [M1]; exact I.saves) hret (by rw [q19]; exact sRC)
      (by rw [q19]; exact sRS)
    rw [q19, M1] at h
    exact AcRet.pre c1 (q 3 (by decide)) (q 4 (by decide)) h

/-! ### The stack below the frame

`sigstore::verify` writes up to 0x1A0 bytes below `B`, so the closure's stack
is the 0x5C10 bytes from `B + 0xFFFFFE60`, not the frame's 0x5A70 from `B`.
A stage that calls it keeps `AcInvW` instead of `AcInv`. -/

/-- `AcInv`, with memory kept outside the 0x5C10 bytes from `B + 0xFFFFFE60`:
the frame and the 0x1A0 bytes below it. -/
structure AcInvW (B Bf g t : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (n : Machine) : Prop where
  sp : reg n sp = B + 0x3A50
  gp : reg n (3 : Fin 32) = g
  tp : reg n (4 : Fin 32) = t
  saves : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k
  out : ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → Sep x 1 Bf acBufLen → n.mem x = M0 x

/-- A byte outside the closure's whole stack is outside its frame. -/
theorem acw_frame {B x : Word} (h : Sep x 1 (B + 0xFFFFFE60) 0x5C10) : Sep x 1 B 0x5A70 := by
  have := h.subR (c := 0x1A0) (l := 0x5A70) (by decide)
  have e : B + 0xFFFFFE60 + BitVec.ofNat 32 0x1A0 = B := by
    rw [BitVec.add_assoc]
    exact (congrArg (B + ·) (by decide : (0xFFFFFE60 : Word) + BitVec.ofNat 32 0x1A0 = 0)).trans (BitVec.add_zero B)
  rwa [e] at this

/-- `AcInv` gives `AcInvW`, so a stage that keeps `AcInvW` can follow one
that keeps `AcInv`. -/
theorem AcInv.wide {B Bf g t : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n : Machine}
    (I : AcInv B Bf g t v M0 n) : AcInvW B Bf g t v M0 n :=
  ⟨I.sp, I.gp, I.tp, I.saves, fun x hw hb => I.out x (acw_frame hw) hb⟩

/-- What the `None` exit leaves after a stage that keeps `AcInvW`: 0xFF at
`r + 0xC`, and memory outside the closure's whole stack, `Buffers`, and
`r + 0xC` as it was in `M0`. -/
abbrev AcNoneW (B Bf r : Word) (M0 M' : Word → BitVec 8) : Prop :=
  M' (r + 0xC) = 0xFF ∧
    ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → Sep x 1 Bf acBufLen → Sep x 1 (r + 0xC) 1 → M' x = M0 x

/-- **`ac_exit` from `AcInvW`**: every way into an exit returns `None`, with
memory as `AcNoneW` says. -/
theorem ac_exit_wide {romBase : Word} {romCode : List Nat} {romStack : Nat}
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (hrs : romStack ≤ 0x3A50)
    {n : Machine} {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8}
    (C : CodeIn n.mem AC bootMainClosure0Code) (CR : CodeIn n.mem romBase romCode)
    (T : CodeIn n.mem (BitVec.ofNat 32 acRejectTableAddress) acRejectTableData)
    (sRB : Sep B 0x5A70 romBase romCode.length) (F : Fr B 0x5A70) (hret : v 0 &&& ~~~1 = v 0)
    (sRC : Sep (r + 0xC) 1 AC bootMainClosure0Code.length) (sRS : Sep (r + 0xC) 1 B 0x5A70)
    (I : AcInvW B Bf g t v M0 n) (h : AcFail B r n) :
    AcRet B v n (AcNoneW B Bf r M0) :=
  (ac_exit (Bf := Bf) (g := reg n (3 : Fin 32)) (t := reg n (4 : Fin 32)) (M0 := n.mem) log hrs C CR T sRB F hret
    sRC sRS ⟨I.sp, rfl, rfl, I.saves, fun _ _ _ => rfl⟩ h).mono
    fun _ ⟨hF, hK⟩ => ⟨hF, fun x hw hb hr => (hK x (acw_frame hw) hr).trans (I.out x hw hb)⟩

end C3.RV32.Ac
