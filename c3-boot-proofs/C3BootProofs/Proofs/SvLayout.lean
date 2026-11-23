import C3BootProofs.Proofs.SvVerify

/-!
# `sigstore::verify`: how its arguments lie in memory

`sv_verify` states what it needs of the bundle and the trust root as facts
about words and slices at fixed offsets from `a1` and `a2`. The predicates
here say instead that a `Bundle` and a `SigstoreRoot`, the values that
`sigstoreVerify` takes, lie at those addresses in the layout `rustc` chose:

- `Bundle` (0x30 bytes): the leaf certificate's slice at 0x0, the image
  signature's at 0x8, the inclusion proof's at 0x10, the checkpoint's at
  0x18, the timestamp's at 0x20, and the log index at 0x28.
- `TrustRoot` (0x238 bytes): the policy's five slices at 0x0, then arrays of
  4 Fulcio intermediates at 0x38, 8 logs at 0xB8, and 4 TSAs at 0x1B8.
  Each entry is 0x20 bytes: its name's slice, its window's two 64-bit
  bounds at 0x8 and 0x10, and a pointer to its key at 0x18. The entries
  after the listed ones have a null name pointer, as `Option` encodes
  `None`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3

/-- `bs`, the `l` bytes at `p`, outside the stack. -/
def SvBytesAt (B : Word) (M : Word → BitVec 8) (p l : Word) (bs : Bytes) : Prop :=
  SvIn B p l.toNat ∧ memBytes M p l.toNat = bs

/-- `bs`, the `l` bytes at `p`, outside the stack or among the image's constants. -/
def SvRoBytesAt (B : Word) (M : Word → BitVec 8) (p l : Word) (bs : Bytes) : Prop :=
  SvRo B p l.toNat ∧ memBytes M p l.toNat = bs

/-- The 64-bit number `x` in the two words at `a`, low word first. -/
def SvU64At (M : Word → BitVec 8) (a : Word) (x : Nat) : Prop :=
  x < 2 ^ 64 ∧ memLoad32 M a = BitVec.ofNat 32 x ∧ memLoad32 M (a + 4) = BitVec.ofNat 32 (x / 2 ^ 32)

/-- A listed trust-root entry at `e`: its name, its validity window, and the
`n`-byte key its pointer at 0x18 points at. -/
structure SvEntryAt (B : Word) (M : Word → BitVec 8) (e : Word) (name key : Bytes) (n : Nat) (w : Window) :
    Prop where
  ne : memLoad32 M e ≠ 0
  name : SvBytesAt B M (memLoad32 M e) (memLoad32 M (e + 4)) name
  notBefore : SvU64At M (e + 8) w.notBefore
  notAfter : SvU64At M (e + 0x10) w.notAfter
  keyIn : SvIn B (memLoad32 M (e + 0x18)) n
  key : memBytes M (memLoad32 M (e + 0x18)) n = key

/-- The entries `l` of an array of `cap` entries 0x20 bytes apart at `a`:
each listed one as `f` says, and a null name pointer after them. -/
def SvArrayAt {α : Type} (M : Word → BitVec 8) (a : Word) (cap : Nat) (l : List α)
    (f : Word → α → Prop) : Prop :=
  l.length ≤ cap ∧ (∀ i (h : i < l.length), f (a + BitVec.ofNat 32 (0x20 * i)) l[i]) ∧
    ∀ i, l.length ≤ i → i < cap → memLoad32 M (a + BitVec.ofNat 32 (0x20 * i)) = 0

/-- A `SigstoreRoot`, as the `TrustRoot` struct at `r`. -/
structure SvRootAt (B : Word) (M : Word → BitVec 8) (r : Word) (root : SigstoreRoot) : Prop where
  al : r.toNat % 4 = 0
  inn : SvIn B r 0x238
  issuer : SvRoBytesAt B M (memLoad32 M r) (memLoad32 M (r + 0x4)) root.policy.issuer
  buildSignerUri : SvRoBytesAt B M (memLoad32 M (r + 0x8)) (memLoad32 M (r + 0xC)) root.policy.buildSignerUri
  repositoryId : SvRoBytesAt B M (memLoad32 M (r + 0x10)) (memLoad32 M (r + 0x14)) root.policy.repositoryId
  ownerId : SvRoBytesAt B M (memLoad32 M (r + 0x18)) (memLoad32 M (r + 0x1C)) root.policy.ownerId
  trigger : SvRoBytesAt B M (memLoad32 M (r + 0x20)) (memLoad32 M (r + 0x24)) root.policy.trigger
  fulcio : SvArrayAt M (r + 0x38) 4 root.fulcio fun e k => SvEntryAt B M e k.subject k.publicKey 0x61 k.window
  logs : SvArrayAt M (r + 0xB8) 8 root.logs fun e k => SvEntryAt B M e k.origin k.publicKey 32 k.window
  tsas : SvArrayAt M (r + 0x1B8) 4 root.tsas fun e k => SvEntryAt B M e k.signerId k.publicKey 0x61 k.window

/-- A `Bundle`, as the struct at `bp`. -/
structure SvBundleAt (B : Word) (M : Word → BitVec 8) (bp : Word) (b : Bundle) : Prop where
  al : bp.toNat % 4 = 0
  inn : SvIn B bp 0x30
  leaf : SvBytesAt B M (memLoad32 M bp) (memLoad32 M (bp + 4)) b.leafCertificate
  imageSignature : SvBytesAt B M (memLoad32 M (bp + 0x8)) (memLoad32 M (bp + 0xC)) b.imageSignature
  inclusionProof : SvBytesAt B M (memLoad32 M (bp + 0x10)) (memLoad32 M (bp + 0x14)) b.inclusionProof
  checkpoint : SvBytesAt B M (memLoad32 M (bp + 0x18)) (memLoad32 M (bp + 0x1C)) b.checkpoint
  timestamp : SvBytesAt B M (memLoad32 M (bp + 0x20)) (memLoad32 M (bp + 0x24)) b.timestamp
  logIndex : SvU64At M (bp + 0x28) b.logIndex

/-- Bytes inside a slice outside the stack are outside it too. -/
theorem SvIn.sub {B p : Word} {n c l : Nat} (h : SvIn B p n) (hc : c + l ≤ n) :
    SvIn B (p + BitVec.ofNat 32 c) l := by
  have hlo := h.lo
  have e : (p + BitVec.ofNat 32 c).toNat = p.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact ⟨h.sep14.sub (c := c) (l := l + 14) (by omega), by rw [e]; have := h.pos; omega, by rw [e]; omega⟩

theorem SvIn.ptr {B p q : Word} {n : Nat} (h : SvIn B p n) (e : q = p) : SvIn B q n := e ▸ h

/-- An aligned word inside an aligned slice. -/
theorem SvIn.word {B p : Word} {n c : Nat} (h : SvIn B p n) (al : p.toNat % 4 = 0) (hc : c + 4 ≤ n)
    (h4 : c % 4 = 0) : SvIn B (p + BitVec.ofNat 32 c) 4 ∧ (p + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  have hlo := h.lo
  refine ⟨h.sub hc, ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem SvIn.wordAt {B p q : Word} {n c : Nat} (h : SvIn B p n) (al : p.toNat % 4 = 0) (hc : c + 4 ≤ n)
    (h4 : c % 4 = 0) (e : q = p + BitVec.ofNat 32 c) : SvIn B q 4 ∧ q.toNat % 4 = 0 := e ▸ h.word al hc h4

theorem SvIn.load {B p q : Word} {M : Word → BitVec 8} {n : Nat} (h : SvIn B (memLoad32 M p) n) (e : q = p) :
    SvIn B (memLoad32 M q) n := e ▸ h

theorem SvIn.load2 {B p q p' q' : Word} {M : Word → BitVec 8} (h : SvIn B (memLoad32 M p) (memLoad32 M q).toNat)
    (e : p' = p) (e' : q' = q) : SvIn B (memLoad32 M p') (memLoad32 M q').toNat := e ▸ e' ▸ h

theorem SvRo.load2 {B p q p' q' : Word} {M : Word → BitVec 8} (h : SvRo B (memLoad32 M p) (memLoad32 M q).toNat)
    (e : p' = p) (e' : q' = q) : SvRo B (memLoad32 M p') (memLoad32 M q').toNat := e ▸ e' ▸ h

/-- The bundle struct sits apart from the saved registers. -/
theorem SvBundleAt.sep {B bp : Word} {M : Word → BitVec 8} {b : Bundle} (Bd : SvBundleAt B M bp b) :
    Sep bp 8 (B + BitVec.ofNat 32 0x37FC) 0x34 := by
  have h := (Bd.inn.sep14.sub (c := 0) (l := 8) (by decide)).symm.sub (c := 0x399C) (l := 0x34) (by decide)
  rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 0x399C = B + BitVec.ofNat 32 0x37FC by bv_omega,
    add_ofNat_zero] at h
  exact h.symm

/-- A listed entry of an array, from its name pointer being non-null. -/
theorem SvArrayAt.listed {α : Type} {M : Word → BitVec 8} {a : Word} {cap i : Nat} {l : List α}
    {f : Word → α → Prop} (A : SvArrayAt M a cap l f) (hi : i < cap)
    (hne : memLoad32 M (a + BitVec.ofNat 32 (0x20 * i)) ≠ 0) :
    ∃ h : i < l.length, f (a + BitVec.ofNat 32 (0x20 * i)) l[i] := by
  by_cases hl : i < l.length
  · exact ⟨hl, A.2.1 i hl⟩
  · exact absurd (A.2.2 i (by omega) hi) hne

/-- A search's pointer after `i` steps of 0x20 bytes. -/
theorem svIter_ptr2 {d : Word} {c q y0 y1 : Word} {i : Nat}
    (h : (y0, y1) = svIter (fun s => (s.1 + d, s.2 + BitVec.ofNat 32 0x20)) i (c, q)) :
    y1 = q + BitVec.ofNat 32 (i * 0x20) :=
  (congrArg Prod.snd h).trans (svIter_add Prod.snd (by intro _; rfl) i (c, q))

theorem svIter_ptr3 {d : Word} {f : Word × Word × Word → Word} {c q w y0 y1 y2 : Word} {i : Nat}
    (h : (y0, y1, y2) = svIter (fun s => (s.1 + d, s.2.1 + BitVec.ofNat 32 0x20, f s)) i (c, q, w)) :
    y1 = q + BitVec.ofNat 32 (i * 0x20) :=
  (congrArg (fun s => s.2.1) h).trans (svIter_add (fun s => s.2.1) (by intro _; rfl) i (c, q, w))

end C3.RV32.Sv
