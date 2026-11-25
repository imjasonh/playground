import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Constructor
import C3BootProofs.Proofs.AcceptSpec
import C3BootProofs.Proofs.LoadedImage

/-!
# The first closure's memory condition from the loaded image

`acl_acsE` shows `AcsE` for the image's pinned root `acPinnedRootData` and
policy `imagePolicy` in every memory that agrees outside RAM with one that
holds the image (`Loaded`) and the ROM's code.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract

/-- The identity policy that the image holds: the strings that `acPolicy`
and the closure's code point to. -/
def imagePolicy : Policy :=
  ⟨acIssuerData, acBuildSignerUriData, acRepositoryIdData, acOwnerIdData, acTriggerData⟩

/-- The last listed piece of the image that starts at or below `a`. -/
def pieceAt (a : Nat) : Option (Nat × List Nat) :=
  imagePieces.foldl (fun acc p => if p.1 ≤ a then some p else acc) none

/-- The piece of the image at `a` holds `c` there. -/
def imageHas (a : Nat) (c : List Nat) : Bool :=
  match pieceAt a with
  | some p => decide (p.1 ≤ a) && decide (a + c.length ≤ p.1 + p.2.length) &&
      decide ((p.2.drop (a - p.1)).take c.length = c)
  | none => false

/-- The `n` bytes at `a` of the piece of the image at `a`. -/
def imageBytes (a n : Nat) : List Nat :=
  match pieceAt a with
  | some p => (p.2.drop (a - p.1)).take n
  | none => []

theorem acl_foldl {a : Nat} {p : Nat × List Nat} :
    ∀ (l : List (Nat × List Nat)) (acc : Option (Nat × List Nat)),
      l.foldl (fun acc p => if p.1 ≤ a then some p else acc) acc = some p → p ∈ l ∨ acc = some p
  | [], _, h => .inr h
  | q :: l, acc, h => by
    rcases acl_foldl l _ h with h | h
    · exact .inl (List.mem_cons_of_mem q h)
    · have h : (if q.1 ≤ a then some q else acc) = some p := h
      by_cases hq : q.1 ≤ a
      · simp only [hq, ↓reduceIte] at h
        cases h
        exact .inl List.mem_cons_self
      · simp only [hq, ↓reduceIte] at h
        exact .inr h

theorem acl_code {M : Word → BitVec 8} (L : Loaded M) {b : Word} {c : List Nat} (h : imageHas b.toNat c = true) :
    CodeIn M b c := by
  unfold imageHas at h
  cases hp : pieceAt b.toNat with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    have hm : p ∈ imagePieces := by
      rcases acl_foldl imagePieces none hp with h' | h'
      · exact h'
      · cases h'
    obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hm
    have hL := L k hk
    rw [hkp] at hL
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have h1 := of_decide_eq_true h1
    have h2 := of_decide_eq_true h2
    have h3 := of_decide_eq_true h3
    have := CodeIn.sub hL (b.toNat - p.1) (small := c) (by omega) h3.symm
    rwa [show p.1 + (b.toNat - p.1) = b.toNat by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem acl_bytes {M : Word → BitVec 8} (L : Loaded M) {b : Word} {n : Nat} {c : List Nat}
    (h : (imageHas b.toNat c && c.all (· < 256) && decide (c.length = n)) = true) : memBytes M b n = c := by
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [← of_decide_eq_true h3]
  exact tuf_codeIn_memBytes (acl_code L h1) fun x hx => of_decide_eq_true (List.all_eq_true.mp h2 x hx)

theorem acl_panic {M : Word → BitVec 8} (L : Loaded M)
    (h : panicFns.all (fun p => decide (p.1 < 2 ^ 32) && imageHas p.1 p.2) = true) : PanicCode M := by
  intro p hp
  have hq := List.all_eq_true.mp h p hp
  rw [Bool.and_eq_true] at hq
  have e : (BitVec.ofNat 32 p.1).toNat = p.1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (of_decide_eq_true hq.1)
  exact acl_code L (by rw [e]; exact hq.2)

/-- The bytes of `c` from `a`, and 0 past them. -/
def codeMem (a : Word) (c : List Nat) : Word → BitVec 8 := fun x => byteAt c (x - a).toNat

theorem acl_s5 {M : Word → BitVec 8} (L : Loaded M) {a : Word}
    (h : (imageHas a.toNat sha512IVData && decide (sha512IVData.length = 64)) = true)
    (hv : (s5Hv (codeMem a sha512IVData) a).toList = Sha512.h0) : (s5Hv M a).toList = Sha512.h0 := by
  rw [Bool.and_eq_true] at h
  have C := acl_code L h.1
  have hl := of_decide_eq_true h.2
  rw [← hv, s5Hv_congr (M := codeMem a sha512IVData)]
  intro i hi
  rw [C i (by omega)]
  unfold codeMem
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- A value read from the `n` bytes at `a` is its value in `codeMem`. -/
theorem acl_val {α : Type} {M : Word → BitVec 8} (L : Loaded M) {a : Word} {c : List Nat} {n : Nat}
    (f : (Word → BitVec 8) → α)
    (hf : ∀ M M' : Word → BitVec 8, (∀ i, i < n → M' (a + BitVec.ofNat 32 i) = M (a + BitVec.ofNat 32 i)) →
      f M' = f M)
    (h : (imageHas a.toNat c && decide (n ≤ c.length) && decide (n ≤ 2 ^ 32)) = true) {v : α}
    (hv : f (codeMem a c) = v) : f M = v := by
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  have C := acl_code L h.1.1
  have hl := of_decide_eq_true h.1.2
  have hn := of_decide_eq_true h.2
  rw [← hv]
  refine hf _ _ fun i hi => ?_
  rw [C i (by omega)]
  unfold codeMem
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem acl_fe {M : Word → BitVec 8} (L : Loaded M) {a : Word} {v : List Nat}
    (h : (imageHas a.toNat (imageBytes a.toNat 40) && decide (40 ≤ (imageBytes a.toNat 40).length) &&
      decide (40 ≤ 2 ^ 32)) = true)
    (hv : feW (codeMem a (imageBytes a.toNat 40)) a = v) : feW M a = v := by
  refine acl_val L (fun M => feW M a) (fun M M' hM => ?_) h hv
  have e : ∀ k, k < 10 → limbAt M' a k = limbAt M a k := fun k hk => by
    exact congrArg BitVec.toNat (memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hM _ (by omega))
  show feW M' a = feW M a
  unfold feW
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide)]

theorem acl_acc {M : Word → BitVec 8} (L : Loaded M) {a : Word} {k v : Nat}
    (h : (imageHas a.toNat (imageBytes a.toNat (4 * k)) && decide (4 * k ≤ (imageBytes a.toNat (4 * k)).length) &&
      decide (4 * k ≤ 2 ^ 32)) = true)
    (hv : accV (codeMem a (imageBytes a.toNat (4 * k))) a k = v) : accV M a k = v :=
  acl_val L (fun M => accV M a k)
    (fun _ _ hM => accV_congr k fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hM _ (by omega)) h hv

theorem acl_lz {M : Word → BitVec 8} (L : Loaded M) {a : Word} {k v : Nat}
    (h : (imageHas a.toNat (imageBytes a.toNat (4 * k)) && decide (4 * k ≤ (imageBytes a.toNat (4 * k)).length) &&
      decide (4 * k ≤ 2 ^ 32)) = true)
    (hv : lzLimbs (codeMem a (imageBytes a.toNat (4 * k))) a k = v) : lzLimbs M a k = v :=
  acl_val L (fun M => lzLimbs M a k)
    (fun _ _ hM => lz_congr k fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hM _ (by omega)) h hv

open Lean Elab Tactic Meta in
/-- Proves a code condition from `Loaded` in the context: each piece of code
or data from the image, a structure of them field by field, and the ROM's
code from the context. -/
partial def aclEnvCore : TacticM Unit := do
  let g ← getMainGoal
  let t0 ← instantiateMVars (← g.getType)
  let t ← if (t0.getAppFn.constName? matches some ``CodeIn) then pure t0 else whnfR t0
  let leaf (tac : TSyntax `tactic) : TacticM Unit :=
    try Term.withoutErrToSorry (evalTactic tac)
    catch e => throwError m!"acl_env: not from the image: {t}: {e.toMessageData}"
  match t.getAppFn.constName? with
  | some ``CodeIn =>
    if (t.getArg! 1).isFVar then evalTactic (← `(tactic| assumption))
    else leaf (← `(tactic| exact acl_code ‹Loaded _› (by decide +kernel)))
  | some ``PanicCode => leaf (← `(tactic| exact acl_panic ‹Loaded _› (by decide +kernel)))
  | some ``Eq =>
    leaf (← match (t.getArg! 1).getAppFn.constName? with
      | some ``memBytes => `(tactic| exact acl_bytes ‹Loaded _› (by decide +kernel))
      | some ``feW => `(tactic| exact acl_fe ‹Loaded _› (by decide +kernel) (by decide +kernel))
      | some ``accV => `(tactic| exact acl_acc ‹Loaded _› (by decide +kernel) (by decide +kernel))
      | some ``lzLimbs => `(tactic| exact acl_lz ‹Loaded _› (by decide +kernel) (by decide +kernel))
      | _ => `(tactic| exact acl_s5 ‹Loaded _› (by decide +kernel) (by decide +kernel)))
  | some ``C3.RV32.EdM.EdImage =>
    for g' in ← g.apply (mkConst ``C3.RV32.EdM.EdImage.ofCode) do
      setGoals [g']
      aclEnvCore
    setGoals []
  | _ =>
    let t' ← whnf t
    let gs ← (← g.replaceTargetDefEq t').constructor
    for g' in gs do
      setGoals [g']
      aclEnvCore
    setGoals []

elab "acl_env" : tactic => aclEnvCore

theorem acl_byte {S : Word → BitVec 8} {p : Word} {n : Nat} {c : List Nat} (h : memBytes S p n = c) {i : Nat}
    (hi : i < n) : S (p + BitVec.ofNat 32 i) = BitVec.ofNat 8 (c.getD i 0) := by
  rw [← h, memBytes_getD hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem acl_load {S : Word → BitVec 8} {p : Word} {n : Nat} {c : List Nat} (h : memBytes S p n = c) {k : Nat}
    (hk : k + 4 ≤ n) :
    memLoad32 S (p + BitVec.ofNat 32 k) = BitVec.ofNat 8 (c.getD (k + 3) 0) ++ BitVec.ofNat 8 (c.getD (k + 2) 0) ++
      BitVec.ofNat 8 (c.getD (k + 1) 0) ++ BitVec.ofNat 8 (c.getD k 0) := by
  unfold memLoad32
  rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc,
    acl_byte h (i := k + 3) (by omega), acl_byte h (i := k + 2) (by omega), acl_byte h (i := k + 1) (by omega),
    acl_byte h (i := k) (by omega)]

/-- A policy string at `p`, `l` bytes long, read-only for `sigstore::verify`
on a frame at `B`. -/
theorem acl_str {M S : Word → BitVec 8} (L : Loaded M) (hS : ∀ x, AcsOutRam x → S x = M x) {B p l : Word}
    {c : List Nat} (hB : 0x3FCC81A0 ≤ B.toNat) (hB2 : B.toNat + 0x5A70 ≤ 0x3FCE0000)
    (h : (imageHas p.toNat c && c.all (· < 256) && decide (0 < p.toNat) &&
      decide (p.toNat + c.length + 14 ≤ 0x3FCC8000) && decide (l.toNat = c.length)) = true) :
    Sv.SvRoBytesAt (B + 0x13F0) S p l c := by
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h3 := of_decide_eq_true h3
  have h4 := of_decide_eq_true h4
  have h5 := of_decide_eq_true h5
  have e : (B + 0x13F0 + 0xFFFFEA70 : Word).toNat = B.toNat - 0x1A0 := by
    have := B.isLt
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
  unfold Sv.SvRoBytesAt Sv.SvRo
  rw [h5]
  refine ⟨.inl ⟨sep_of_le (by omega) (by omega), h3, by omega⟩, ?_⟩
  rw [memBytes_congr (M := M) fun i hi => hS _ (.inl (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
  exact acl_bytes L (Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨h1, h2⟩, decide_eq_true rfl⟩)

/-- The policy that the closure hands `sigstore::verify` is `imagePolicy`. -/
theorem acl_pol {M : Word → BitVec 8} (L : Loaded M) (B a : Word) (S : Word → BitVec 8)
    (hB : 0x3FCC81A0 ≤ B.toNat) (hB2 : B.toNat + 0x5A70 ≤ 0x3FCE0000) (hS : ∀ x, AcsOutRam x → S x = M x)
    (h1 : memLoad32 S a = 0x3FCC6621) (h2 : S (a + 4) = 0x2B)
    (h3 : memBytes S (a + 5) 0x23 = memBytes M (img% acPolicyAddress) 0x23) :
    AcsPolicyAt (B + 0x13F0) S a imagePolicy := by
  have hP : memBytes S (a + BitVec.ofNat 32 5) 0x23 = acPolicyData := h3.trans (acl_bytes L (by decide +kernel))
  have ld : ∀ k, k + 4 ≤ 0x23 → ∀ o : Word, o = BitVec.ofNat 32 (5 + k) →
      memLoad32 S (a + o) = BitVec.ofNat 8 (acPolicyData.getD (k + 3) 0) ++
        BitVec.ofNat 8 (acPolicyData.getD (k + 2) 0) ++ BitVec.ofNat 8 (acPolicyData.getD (k + 1) 0) ++
        BitVec.ofNat 8 (acPolicyData.getD k 0) := by
    intro k hk o ho
    rw [ho, ← add_ofNat_assoc]
    exact acl_load hP hk
  have l4 : memLoad32 S (a + 0x4) = 0x2B := by
    unfold memLoad32
    have b := fun i (hi : i < 0x23) => acl_byte hP (i := i) hi
    rw [show a + 0x4 + 3 = a + BitVec.ofNat 32 5 + BitVec.ofNat 32 2 by bv_omega,
      show a + 0x4 + 2 = a + BitVec.ofNat 32 5 + BitVec.ofNat 32 1 by bv_omega,
      show a + 0x4 + 1 = a + BitVec.ofNat 32 5 + BitVec.ofNat 32 0 by bv_omega,
      b 2 (by decide), b 1 (by decide), b 0 (by decide), h2]
    decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, l4]; exact acl_str L hS hB hB2 (by decide +kernel)
  · rw [ld 3 (by decide) 0x8 (by decide), ld 7 (by decide) 0xC (by decide)]
    exact acl_str L hS hB hB2 (by decide +kernel)
  · rw [ld 11 (by decide) 0x10 (by decide), ld 15 (by decide) 0x14 (by decide)]
    exact acl_str L hS hB hB2 (by decide +kernel)
  · rw [ld 19 (by decide) 0x18 (by decide), ld 23 (by decide) 0x1C (by decide)]
    exact acl_str L hS hB hB2 (by decide +kernel)
  · rw [ld 27 (by decide) 0x20 (by decide), ld 31 (by decide) 0x24 (by decide)]
    exact acl_str L hS hB hB2 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The closure's callees, data, pinned root, and policy, in memory that
holds the image and the ROM's code. -/
theorem acl_envs {M : Word → BitVec 8} (L : Loaded M) {romBase : Word} {romCode : List Nat}
    (hrom : CodeIn M romBase romCode) : AcsEnvs romBase romCode acPinnedRootData imagePolicy M := by
  constructor
  case pol => exact acl_pol L
  all_goals acl_env

/-- **`AcsE` from the loaded image**: in memory that agrees outside RAM with
memory that holds the image and the ROM's code. -/
theorem acl_acsE {M0 M : Word → BitVec 8} (L : Loaded M0) {romBase : Word} {romCode : List Nat}
    (hrom : CodeIn M0 romBase romCode) (hrb : 0x40000000 ≤ romBase.toNat)
    (hrl : romBase.toNat + romCode.length ≤ 2 ^ 32) (hM : ∀ x, AcsOutRam x → M x = M0 x) :
    AcsE romBase romCode acPinnedRootData imagePolicy M := by
  intro M' hM'
  have h : ∀ x, AcsOutRam x → M' x = M0 x := fun x hx => (hM' x hx).trans (hM x hx)
  refine acl_envs (L.congr fun x hx => h x ?_) fun i hi => ?_
  · rcases hx with ⟨_, hx⟩ | ⟨hx, _⟩
    · exact .inl hx
    · exact .inr (by omega)
  · rw [h _ (.inr (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))]
    exact hrom i hi

end C3.RV32.Ac

