import C3BootProofs.Proofs.SvPv
import C3BootProofs.Proofs.DerOid

/-!
# `sigstore::verify`: what `p384_verify_prehash`'s model reads

`pvModel` reads the key's 97 bytes, at most 48 bytes of the prehash, `r` and
`s`, and the scalar range's bound, so two memories that agree on those give
the same result.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

theorem pvModel_congr {M M' : Word → BitVec 8} {pk ph rp sp' : Word} {len : Nat}
    (hk : memBytes M pk 0x61 = memBytes M' pk 0x61)
    (hh : memBytes M ph (min len 48) = memBytes M' ph (min len 48))
    (hr : memBytes M rp 48 = memBytes M' rp 48) (hs : memBytes M sp' 48 = memBytes M' sp' 48)
    (hn : memBytes M ISRN 48 = memBytes M' ISRN 48) :
    pvModel M pk ph len rp sp' = pvModel M' pk ph len rp sp' := by
  have hv : ∀ o, o + 48 ≤ 0x61 → Fs.fsVal M pk o = Fs.fsVal M' pk o := fun o ho => by
    unfold Fs.fsVal; rw [← memBytes_drop_take ho, ← memBytes_drop_take ho, hk]
  have h0 : M pk = M' pk := by
    have := congrArg (fun l => l[0]?) hk
    simp only [memBytes, List.getElem?_map, List.getElem?_range (show 0 < 0x61 by decide), Option.map_some,
      Option.some.injEq, BitVec.add_zero] at this
    exact BitVec.eq_of_toNat_eq this
  have hw : pvW M sp' = pvW M' sp' := by unfold pvW; rw [hs]
  have hok : Fs.FsOk M pk ↔ Fs.FsOk M' pk := by
    unfold Fs.FsOk; rw [h0, hv 1 (by decide), hv 0x31 (by decide)]
  have hsum : pvSumM M pk ph len rp sp' = pvSumM M' pk ph len rp sp' := by
    unfold pvSumM; rw [hv 1 (by decide), hv 0x31 (by decide), hr, hh, hw]
  unfold pvModel PvCk1 PvCk2
  simp only [hr, hs, hn, hw, hsum, hok]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

/-- The `n` bytes that `n` byte facts `BitVec.ofNat 8 (l.getD j 0)` give. -/
def svBytes (l : Bytes) (n : Nat) : Bytes := (List.range n).map fun j => (BitVec.ofNat 8 (l.getD j 0)).toNat

theorem memBytes_svBytes {M : Word → BitVec 8} {p : Word} {l : Bytes} {n : Nat}
    (h : ∀ j, j < n → M (p + BitVec.ofNat 32 j) = BitVec.ofNat 8 (l.getD j 0)) : memBytes M p n = svBytes l n := by
  unfold memBytes svBytes
  exact List.map_congr_left fun j hj => by rw [h j (List.mem_range.mp hj)]

/-- What `p384_verify_prehash` reads: the key and the scalar range's bound as
in `M0`, the prehash `h` at `ph`, and `r` and `s`, as `sr` and `ss`, at `rp`
and `sp'`. -/
def SvPvAt (M0 M : Word → BitVec 8) (pk ph : Word) (len : Nat) (h : Bytes) (rp sp' : Word) (sr ss : Bytes) :
    Prop :=
  memBytes M pk 0x61 = memBytes M0 pk 0x61 ∧ memBytes M ISRN 48 = memBytes M0 ISRN 48 ∧
    memBytes M ph (min len 48) = h ∧ memBytes M rp 48 = svBytes sr 48 ∧ memBytes M sp' 48 = svBytes ss 48

/-- `p384_verify_prehash` returns `r` on any memory that `SvPvAt` describes. -/
def SvPvRes (M0 : Word → BitVec 8) (pk ph : Word) (len : Nat) (h : Bytes) (rp sp' : Word) (sr ss : Bytes)
    (r : Option Word) : Prop :=
  ∀ M, SvPvAt M0 M pk ph len h rp sp' sr ss → pvModel M pk ph len rp sp' = r

theorem SvPvRes.of {M0 M : Word → BitVec 8} {pk ph rp sp' : Word} {len : Nat} {h sr ss : Bytes}
    (hM : SvPvAt M0 M pk ph len h rp sp' sr ss) : SvPvRes M0 pk ph len h rp sp' sr ss (pvModel M pk ph len rp sp') :=
  fun M' hM' => by
    obtain ⟨k, n, ph, r, s⟩ := hM
    obtain ⟨k', n', ph', r', s'⟩ := hM'
    exact pvModel_congr (k'.trans k.symm) (ph'.trans ph.symm) (r'.trans r.symm) (s'.trans s.symm) (n'.trans n.symm)

/-- `r` or `s` in the frame as one byte and a range after it, or as one range. -/
theorem memBytes_frame1 {B : Word} {M : Word → BitVec 8} {l : Bytes} {e : Nat}
    (h0 : M (B + 0x21A0 + BitVec.ofNat 32 e) = BitVec.ofNat 8 (l.getD 0 0))
    (h1 : ∀ j, j < 47 → M (B + 0x21A0 + BitVec.ofNat 32 (e + 1 + j)) = BitVec.ofNat 8 (l.getD (1 + j) 0)) :
    memBytes M (B + 0x21A0 + BitVec.ofNat 32 e) 48 = svBytes l 48 :=
  memBytes_svBytes fun j hj => by
    rw [add_ofNat_assoc]
    rcases j with _ | i
    · exact h0
    · rw [show e + (i + 1) = e + 1 + i by omega, show i + 1 = 1 + i by omega]; exact h1 i (by omega)

theorem memBytes_frame {B : Word} {M : Word → BitVec 8} {l : Bytes} {e : Nat}
    (h : ∀ j, j < 48 → M (B + 0x21A0 + BitVec.ofNat 32 (e + j)) = BitVec.ofNat 8 (l.getD j 0)) :
    memBytes M (B + 0x21A0 + BitVec.ofNat 32 e) 48 = svBytes l 48 :=
  memBytes_svBytes fun j hj => by rw [add_ofNat_assoc]; exact h j hj

end C3.RV32.Sv
