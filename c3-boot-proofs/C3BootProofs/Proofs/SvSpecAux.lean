import C3BootProofs.Proofs.SvModels
import C3BootProofs.Proofs.SvWinLink
import C3BootProofs.Proofs.SvCosigLink
import C3BootProofs.Proofs.SvConstsLink
import C3BootProofs.Image.BootloaderData6
import C3BootProofs.Proofs.SvRk
import C3BootProofs.Proofs.SvRoot

/-!
# Facts `sv_verify_spec` uses

Lengths and byte ranges of hashes and of the checkpoint signature, the
memory `ed25519_verify` reads, the code's length arithmetic, and the Rekor
entry's constants in the image.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3

theorem codeIn_memBytes {M : Word → BitVec 8} {base : Word} {code : List Nat} (C : CodeIn M base code)
    (hb : ∀ b ∈ code, b < 256) : memBytes M base code.length = code := by
  unfold memBytes
  apply List.ext_getElem
  · rw [List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [C i h2]
    unfold byteAt
    rw [BitVec.toNat_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    exact Nat.mod_eq_of_lt (hb _ (List.getElem_mem h2))

/-- The Rekor entry's constant pieces, where the image puts them. -/
structure SvRekorData (M : Word → BitVec 8) : Prop where
  leaf : CodeIn M (BitVec.ofNat 32 svRekorLeafAddress) svRekorLeafData
  pre : CodeIn M (BitVec.ofNat 32 svRekorPreAddress) svRekorPreData
  mid1 : CodeIn M (BitVec.ofNat 32 svRekorMid1Address) svRekorMid1Data
  mid2 : CodeIn M (BitVec.ofNat 32 svRekorMid2Address) svRekorMid2Data
  post : CodeIn M (BitVec.ofNat 32 svRekorPostAddress) svRekorPostData

theorem SvRekorData.leaf' {M : Word → BitVec 8} (D : SvRekorData M) :
    memBytes M (BitVec.ofNat 32 (img% svRekorLeafAddress)) 1 = [0x00] :=
  codeIn_memBytes D.leaf (by decide)

theorem SvRekorData.pre' {M : Word → BitVec 8} (D : SvRekorData M) :
    memBytes M (BitVec.ofNat 32 (img% svRekorPreAddress)) 0x71 = rekorPre :=
  (codeIn_memBytes D.pre (by decide)).trans (by decide)

theorem SvRekorData.mid1' {M : Word → BitVec 8} (D : SvRekorData M) :
    memBytes M (BitVec.ofNat 32 (img% svRekorMid1Address)) 0x1B = rekorMid1 :=
  (codeIn_memBytes D.mid1 (by decide)).trans (by decide)

theorem SvRekorData.mid2' {M : Word → BitVec 8} (D : SvRekorData M) :
    memBytes M (BitVec.ofNat 32 (img% svRekorMid2Address)) 0x54 = rekorMid2 :=
  (codeIn_memBytes D.mid2 (by decide)).trans (by decide)

theorem SvRekorData.post' {M : Word → BitVec 8} (D : SvRekorData M) :
    memBytes M (BitVec.ofNat 32 (img% svRekorPostAddress)) 7 = rekorPost :=
  (codeIn_memBytes D.post (by decide)).trans (by decide)

/-- The `0x01` of the key ID, which `merkleNodeHash` also prefixes. -/
theorem keyIdOne {M : Word → BitVec 8} (D : SvRkCode M) : memBytes M (BitVec.ofNat 32 (img% merklePrefixAddress)) 1 = [0x01] :=
  codeIn_memBytes D.pre (by decide)

theorem round_length (w : Array Sha256.W32) (v : List Sha256.W32) (t : Nat) : (Sha256.round w v t).length = v.length := by
  unfold Sha256.round
  split <;> rfl

theorem foldl_length {β : Type} {f : List Sha256.W32 → β → List Sha256.W32} (hf : ∀ v t, (f v t).length = v.length) :
    ∀ (l : List β) (v : List Sha256.W32), (l.foldl f v).length = v.length
  | [], _ => rfl
  | t :: l, v => by rw [List.foldl_cons, foldl_length hf l, hf]

theorem compress_length (hv : List Sha256.W32) (block : Bytes) : (Sha256.compress hv block).length = hv.length := by
  unfold Sha256.compress
  rw [List.length_zipWith, foldl_length (round_length _), Nat.min_self]

theorem wordBytes_length : ∀ l : List Sha256.W32, (l.flatMap Sha256.wordBytes).length = 4 * l.length
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, wordBytes_length l, List.length_cons]
    show 4 + 4 * l.length = 4 * (l.length + 1)
    omega

theorem sha256_length (msg : Bytes) : (sha256 msg).length = 32 := by
  unfold sha256
  rw [wordBytes_length, foldl_length compress_length]
  rfl

theorem b32_self {L : Bytes} (hl : L.length = 32) (hb : ∀ b ∈ L, b < 256) : b32 L = L := by
  unfold b32
  apply List.ext_getElem
  · rw [hl, List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [BitVec.toNat_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    exact Nat.mod_eq_of_lt (hb _ (List.getElem_mem h2))

/-- A 32-byte hash. -/
def IsHash (r : Bytes) : Prop := r.length = 32 ∧ ∀ b ∈ r, b < 256

theorem sha256_hash (msg : Bytes) : IsHash (sha256 msg) := ⟨sha256_length msg, sha256_lt msg⟩

theorem inclusionPath_hash : ∀ {ps : List Bytes} {f s : Nat} {r : Bytes} {s' : Nat} {r' : Bytes},
    inclusionPath f s r ps = some (s', r') → IsHash r → IsHash r'
  | [], _, _, _, _, _, h, hr => by
    cases h
    exact hr
  | p :: ps, f, s, r, s', r', h, _ => by
    unfold inclusionPath at h
    by_cases hs : s = 0
    · rw [ite_eq_left hs] at h; cases h
    rw [ite_eq_right hs] at h
    by_cases hc : f % 2 = 1 ∨ f = s
    · rw [ite_eq_left hc] at h
      exact inclusionPath_hash h (sha256_hash _)
    · rw [ite_eq_right hc] at h
      exact inclusionPath_hash h (sha256_hash _)

theorem require_some {b : Bool} {u : Unit} (h : require b = some u) : b = true := by
  unfold require at h
  cases b
  · cases h
  · rfl

theorem rootFromInclusion_hash {index size : Nat} {leaf proof r : Bytes}
    (h : rootFromInclusion index size leaf proof = some r) (hl : IsHash leaf) : IsHash r := by
  unfold rootFromInclusion at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨hs, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨-, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨s, r'⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨-, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact inclusionPath_hash hp hl

/-- The signature `checkpointSigs` kept is 64 bytes. -/
theorem checkpointSigs_sig {origin id : Bytes} : ∀ (fuel : Nat) {L : Bytes} {m : Option Bytes} {s : Bytes},
    checkpointSigs origin id fuel L m = some (some s) → (∀ s0, m = some s0 → s0.length = 64 ∧ ∀ b ∈ s0, b < 256) →
    s.length = 64 ∧ ∀ b ∈ s, b < 256
  | fuel, [], m, s, h, hm => by cases fuel <;> exact hm s (Option.some.inj h)
  | 0, _ :: _, _, _, h, _ => by cases h
  | f + 1, b :: r, m, s, h, hm => by
    rw [cosig_cons (List.cons_ne_nil _ _)] at h
    simp only [Option.bind_eq_bind] at h
    obtain ⟨⟨line, rest⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨afterDash, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨name, enc⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨-, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · exact checkpointSigs_sig f h hm
    · obtain ⟨value, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨-, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · exact checkpointSigs_sig f h hm
      · obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
        have hc := require_some hu
        rw [Bool.and_eq_true] at hc
        refine checkpointSigs_sig f h fun s0 e => ?_
        cases e
        exact ⟨beq_iff_eq.mp hc.1, fun b hb => base64Decode_lt hv b (List.mem_of_mem_drop hb)⟩

/-- `~~~a + b`, the code's `b - a - 1`. -/
theorem notAdd_toNat {a b : Word} (h : a.toNat < b.toNat) :
    (aluEval .xor a (BitVec.ofNat 32 0xFFFFFFFF) + b).toNat = b.toNat - a.toNat - 1 := by
  have hx : (aluEval .xor a (BitVec.ofNat 32 0xFFFFFFFF)).toNat + a.toNat = 2 ^ 32 - 1 := xor_ones_toNat a
  have := b.isLt
  rw [BitVec.toNat_add]
  omega

/-- The code's test that a length is between 1 and 19. -/
theorem len19 {x : Nat} (hx : x < 2 ^ 32)
    (h : ¬ (BitVec.ofNat 32 x + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) :
    1 ≤ x ∧ x ≤ 19 := by
  rw [BitVec.toNat_add, ofNat_toNat_lt hx, ofNat_toNat_lt (by decide), ofNat_toNat_lt (by decide)] at h
  exact ⟨by omega, by omega⟩

theorem sig_frame (B : Word) : B + 0x21A0 + BitVec.ofNat 32 0x420 = B + BitVec.ofNat 32 0x25C0 := by
  rw [BitVec.add_assoc]; rfl

/-- Bytes outside the stack read the same with the signature written. -/
theorem memBytes_sigMem_in {M : Word → BitVec 8} {B p : Word} {n k : Nat} {L : Bytes} (h : SvIn B p n) (hk : k ≤ n) :
    memBytes (sigMem M (B + 0x21A0 + BitVec.ofNat 32 0x420) L) p k = memBytes M p k := by
  apply memBytes_congr
  intro i hi
  apply sigMem_out
  have hs := h.sepLo (c := 0x25C0) (n := 64) (by decide)
  rw [← sig_frame] at hs
  exact (hs.sub (c := i) (l := 1) (by omega)).symm

/-- The 64 bytes at the signature are the signature. -/
theorem memBytes_sigMem_sig {M : Word → BitVec 8} {sig : Word} {L : Bytes} (hl : L.length = 64)
    (hb : ∀ b ∈ L, b < 256) : memBytes (sigMem M sig L) sig 64 = L := by
  unfold memBytes
  apply List.ext_getElem
  · rw [hl, List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < 64 := by rw [List.length_map, List.length_range] at h1; exact h1
    simp only [List.getElem_map, List.getElem_range]
    rw [sigMem_in hi, BitVec.toNat_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    exact Nat.mod_eq_of_lt (hb _ (List.getElem_mem h2))

theorem pair64_ofNat {t : Nat} (ht : t < 2 ^ 64) : pair64 (BitVec.ofNat 32 t) (BitVec.ofNat 32 (t / 2 ^ 32)) = t := by
  unfold pair64
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_mod32 (x : Nat) : BitVec.ofNat 32 (x % 2 ^ 32) = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]

/-- The code's `x ≤ t` for the 64-bit `x` at `a`. -/
theorem win_ge {M : Word → BitVec 8} {a : Word} {x t : Nat} (hU : SvU64At M a x) (ht : t < 2 ^ 64)
    (h : (memLoad32 M (a + 4) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
        aluEval .sltu (BitVec.ofNat 32 (t % 2 ^ 32)) (memLoad32 M a) = 0) ∨
      (¬ memLoad32 M (a + 4) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
        aluEval .sltu (BitVec.ofNat 32 (t / 2 ^ 32)) (memLoad32 M (a + 4)) = 0)) : x ≤ t := by
  rw [hU.2.1, hU.2.2] at h
  have := win_le h
  rwa [pair64_ofNat hU.1, pair64_halves ht] at this

/-- The code's `t ≤ x` for the 64-bit `x` at `a`. -/
theorem win_le' {M : Word → BitVec 8} {a : Word} {x t : Nat} (hU : SvU64At M a x) (ht : t < 2 ^ 64)
    (h : (BitVec.ofNat 32 (t / 2 ^ 32) = memLoad32 M (a + 4) ∧
        aluEval .sltu (memLoad32 M a) (BitVec.ofNat 32 (t % 2 ^ 32)) = 0) ∨
      (¬ BitVec.ofNat 32 (t / 2 ^ 32) = memLoad32 M (a + 4) ∧
        aluEval .sltu (memLoad32 M (a + 4)) (BitVec.ofNat 32 (t / 2 ^ 32)) = 0)) : t ≤ x := by
  rw [hU.2.1, hU.2.2] at h
  have := win_le h
  rwa [pair64_ofNat hU.1, pair64_halves ht] at this

theorem log_addr {r q : Word} {i : Nat} (h : q = r + BitVec.ofNat 32 0x108 + BitVec.ofNat 32 (i * 0x20)) :
    q + 0x20 = r + 0x128 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x24 = r + 0x128 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      q + BitVec.ofNat 32 0x20 = r + 0x128 + BitVec.ofNat 32 (0x20 * i) := by
  subst h
  rw [Nat.mul_comm i 0x20]
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem fulcio_win {q e : Word} (h : q + 0xFFFFFFFC = e) :
    (q + BitVec.ofNat 32 0x20) + 0xFFFFFFE8 = e + 8 + 4 ∧ (q + BitVec.ofNat 32 0x20) + 0xFFFFFFE4 = e + 8 ∧
      (q + BitVec.ofNat 32 0x20) + 0xFFFFFFF0 = e + 0x10 + 4 ∧ (q + BitVec.ofNat 32 0x20) + 0xFFFFFFEC = e + 0x10 := by
  subst h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem tsa_win {q e : Word} (h : q + 0x20 = e) :
    (q + BitVec.ofNat 32 0x20) + 0xC = e + 8 + 4 ∧ (q + BitVec.ofNat 32 0x20) + 0x8 = e + 8 ∧
      (q + BitVec.ofNat 32 0x20) + 0x14 = e + 0x10 + 4 ∧ (q + BitVec.ofNat 32 0x20) + 0x10 = e + 0x10 := by
  subst h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem log_win (e : Word) :
    e + BitVec.ofNat 32 0x5 + BitVec.ofNat 32 7 = e + 8 + 4 ∧ e + BitVec.ofNat 32 0x5 + BitVec.ofNat 32 3 = e + 8 ∧
      e + BitVec.ofNat 32 0x5 + BitVec.ofNat 32 15 = e + 0x10 + 4 ∧ e + BitVec.ofNat 32 0x5 + BitVec.ofNat 32 11 = e + 0x10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

end C3.RV32.Sv
