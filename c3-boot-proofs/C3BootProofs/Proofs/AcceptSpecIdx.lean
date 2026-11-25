import C3BootProofs.Proofs.AcceptSpecDocs
import C3BootProofs.Proofs.AcceptIndex

/-!
# `boot_main`'s first closure: from 0x2A6 to the return

The index stage: what holds at 0x2A6 (`AcsAt2A6`) ends the closure.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract C3.Json

set_option maxHeartbeats 4000000 in
/-- **The index stage, keeping memory**: `AcIndexStage`, and the stage
writes only the frame below `sp + 0x34` and from `sp + 0x244` to the
saves. -/
theorem acs_indexStage (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat)
    (rd : RomRead flash R romBase romCode) (Rl : Nat) (log : RomFn romBase romCode 0x40000040 Rl (fun _ => True))
    (hRl : Rl ≤ 0x3A50) (n : Machine) (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8)
    (E : ∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcIndexEnv romBase romCode M)
    (C : CodeIn n.mem AC bootMainClosure0Code) (F : Fr B 0x5A70) (sRB : Sep B 0x5A70 romBase romCode.length)
    (hR : R ≤ 0x3A50 - 0x150) (hR4 : R % 4 = 0) (s : St n.mem AC n 0x2A6 (reg n))
    (I : AcInv B Bf g t v M0 n) (pre : AcIndexPre B r n) :
    AcStage B Bf g t r v M0 n 0x4E4 fun n' =>
      (∃ parts, decodeTufParts (flashBytes flash (reg n (24 : Fin 32)).toNat (reg n (23 : Fin 32)).toNat) =
        some parts ∧
        AcIndexPost B n (flashBytes flash (reg n (24 : Fin 32)).toNat (reg n (23 : Fin 32)).toNat) parts n') ∧
      AcxKeep B n.mem n'.mem := by
  let P : AcxP := ⟨flash, R, Rl, romBase, romCode, B, Bf, g, t, r, v, M0, n⟩
  have K : AcxK P := ⟨rd, log, hRl, hR, hR4, F, sRB, E, I, pre, C⟩
  have A : AcxC P n := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨n', st, h | ⟨c, S⟩⟩ := acx_to4e4 K A s
  · exact ⟨n', st, .inr ⟨h.1, .inl h.2⟩⟩
  · exact ⟨n', st, .inr ⟨S.ac.inv K, .inr ⟨S.st.pc, acx_post K S, S.ac.keep⟩⟩⟩

theorem acs_fb_dt (f : Nat → BitVec 8) {a L o l : Nat} (h : o + l ≤ L) :
    ((flashBytes f a L).drop o).take l = flashBytes f (a + o) l := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, acx_flen]; omega
  · intro i h1 h2
    simp only [flashBytes, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      Nat.add_assoc]

theorem acs_getD_len (D : List Bytes) (i : Nat) : (D.map List.length).getD i 0 = (D.getD i []).length := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases D[i]? with _ | d <;> rfl

/-- **Where the index puts a document**: for a part at `start` that
decodes, with the index's count and lengths at `sp + 0x34C` and
`sp + 0x244`, document `i` is at its place in flash. -/
theorem acs_doc_at {flash : Nat → BitVec 8} {M : Word → BitVec 8} {B start : Word} {L : Nat} {parts : TufParts}
    (hd : decodeTufParts (flashBytes flash start.toNat L) = some parts) (hL : L < 2 ^ 32)
    (hcnt : memLoad32 M (acSlot B 0x34C) = BitVec.ofNat 32 parts.roots.length)
    (hl : ∀ i, i < parts.roots.length + 2 → (memLoad32 M (acSlot B (0x244 + 4 * i))).toNat =
      ((parts.roots ++ [parts.targets, parts.trustedRoot]).getD i []).length)
    {i : Nat} (hi : i < parts.roots.length + 2) :
    tufIndexDocSpec M (acSlot B 0x244) i = .ok (8 + 4 * (parts.roots.length + 2) +
      (((parts.roots ++ [parts.targets, parts.trustedRoot]).map List.length).take i).sum,
      ((parts.roots ++ [parts.targets, parts.trustedRoot]).getD i []).length) ∧
    flashBytes flash (start.toNat + (8 + 4 * (parts.roots.length + 2) +
      (((parts.roots ++ [parts.targets, parts.trustedRoot]).map List.length).take i).sum))
      ((parts.roots ++ [parts.targets, parts.trustedRoot]).getD i []).length =
      (parts.roots ++ [parts.targets, parts.trustedRoot]).getD i [] := by
  obtain ⟨hm, hsum, hget⟩ := acs_decode_docs hd
  rw [acx_flen] at hsum
  have hDl : (parts.roots ++ [parts.targets, parts.trustedRoot]).length = parts.roots.length + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hml : ((parts.roots ++ [parts.targets, parts.trustedRoot]).map List.length).length =
      parts.roots.length + 2 := by rw [List.length_map, hDl]
  have hmr : maxRoots = 64 := rfl
  have hc : (memLoad32 M (acSlot B 0x244 + 0x108)).toNat = parts.roots.length := by
    rw [show (0x108 : Word) = BitVec.ofNat 32 0x108 from rfl, acf_slot_add, hcnt, BitVec.toNat_ofNat]
    omega
  have hk := tufIndexDocSpec_ok (M := M) (idx := acSlot B 0x244)
    (lens := (parts.roots ++ [parts.targets, parts.trustedRoot]).map List.length)
    (by rw [hml, hc]) (by rw [hml]; omega)
    (fun j hj => by
      rw [idxLen, acf_slot_add, acs_getD_len]; rw [hml] at hj; exact hl j hj)
    (by rw [hml]; omega) (i := i) (by rw [hml]; exact hi)
  rw [hml, acs_getD_len] at hk
  refine ⟨hk, ?_⟩
  have hle : 8 + 4 * (parts.roots.length + 2) +
      (((parts.roots ++ [parts.targets, parts.trustedRoot]).map List.length).take i).sum +
      ((parts.roots ++ [parts.targets, parts.trustedRoot]).getD i []).length ≤ L := by
    have e := List.take_append_drop (i + 1) ((parts.roots ++ [parts.targets, parts.trustedRoot]).map List.length)
    have e2 := congrArg List.sum e
    rw [List.sum_append, List.take_add_one, List.sum_append, List.getElem?_eq_getElem (by rw [hml]; omega),
      Option.toList_some, List.sum_cons, List.sum_nil] at e2
    rw [← acs_getD_len, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hml]; omega),
      Option.getD_some]
    omega
  rw [← acs_fb_dt flash hle]
  exact (hget i hi).symm

theorem acs_getD_roots {rs : List Bytes} {a b : Bytes} {j : Nat} (h : j < rs.length) :
    (rs ++ [a, b]).getD j [] = rs.getD j [] := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem acs_getD_tg (rs : List Bytes) (a b : Bytes) : (rs ++ [a, b]).getD rs.length [] = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl

theorem acs_getD_tr (rs : List Bytes) (a b : Bytes) : (rs ++ [a, b]).getD (rs.length + 1) [] = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show rs.length + 1 - rs.length = 1 by omega]; rfl

/-- An index entry that `acs_doc_at` places gives `ActDoc`. -/
theorem acs_actDoc {flash : Nat → BitVec 8} {M : Word → BitVec 8} {idx start : Word} {i o l : Nat} {d : Bytes}
    (h1 : tufIndexDocSpec M idx i = .ok (o, l)) (h2 : flashBytes flash (start.toNat + o) l = d) :
    ActDoc flash M idx start i d := fun o' l' e => by
  rw [h1] at e
  cases e; exact h2

theorem acs_sep_out {x B : Word} {N : Nat} (h : Sep x 1 B N) :
    x.toNat < B.toNat ∨ B.toNat + N ≤ x.toNat := by
  rcases Nat.lt_or_ge x.toNat B.toNat with h1 | h1
  · exact .inl h1
  rcases Nat.lt_or_ge x.toNat (B.toNat + N) with h2 | h2
  · refine absurd ?_ (h 0 (by decide) (x.toNat - B.toNat) (by omega))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := x.isLt; omega
  · exact .inr h2

/-- **At 0x2A6**: what the index stage needs, the part's place and length
in `s8` and `s7`, `doc` in `s4`, the bundle in `Buffers`, and what the
image stage left. -/
structure AcsAt2A6 (X : AcsCtx) (mf : Manifest) (header : ImageHeader) (n : Machine) : Prop where
  st : St n.mem AC n 0x2A6 (reg n)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 n
  img : AcsImg X mf header n.mem (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32))
  r24 : (reg n (24 : Fin 32)).toNat = acBase X.slot + mf.tuf.offset
  r23 : (reg n (23 : Fin 32)).toNat = mf.tuf.length
  r20 : reg n (20 : Fin 32) = X.Bf + 0x4000
  res : memLoad32 n.mem (acSlot X.B 0x40) = X.r
  bf : memLoad32 n.mem (acSlot X.B 0x34) = X.Bf
  len : memLoad32 n.mem (acSlot X.B 0x38) = BitVec.ofNat 32 mf.bundle.length
  hL : mf.bundle.length ≤ 0x4000
  bundle : memBytes n.mem X.Bf mf.bundle.length =
    flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length

theorem acs_idxWin {B : Word} (F : Fr B 0x5A70) {M M' : Word → BitVec 8} (h : AcxKeep B M M') {k : Nat}
    (h1 : 0x34 ≤ k) (h2 : k < 0x244) : M' (acSlot B k) = M (acSlot B k) := by
  have e : (acSlot B k).toNat = B.toNat + (0x3A50 + k) := F.at _ (by omega)
  exact h _ (.inr (by rw [e]; omega)) (.inl (by rw [e]; omega))

/-- **From 0x2A6**: the index stage, then the pinned-root stage and the
rest, end the closure. -/
theorem acs_index (hE : AcExtractStage) 
    {X : AcsCtx} (ok : X.Ok) {n : Machine} {mf : Manifest} {header : ImageHeader}
    (S : AcsAt2A6 X mf header n) : X.End n := by
  have E := ok.envsAt S.inv
  refine acs_stage S.inv (acs_indexStage X.flash X.R X.romBase X.romCode ok.rom X.romStack ok.log ok.hrs n
    X.B X.Bf X.g X.t X.r X.v X.M0 (fun M hM => (ok.envs hM).idx) E.ac ok.F ok.sRomB
    (by have := ok.hR; omega) ok.hR4 S.st S.inv S.res) (fun _ => ok.fail)
    fun n' I' hpc ⟨⟨parts, hd, KR, h9, h30, h34, _, _, _, hcnt, hl⟩, K⟩ => ?_
  have hL23 : (reg n (23 : Fin 32)).toNat < 2 ^ 32 := (reg n (23 : Fin 32)).isLt
  have ld : ∀ k, 0x34 ≤ k → k + 4 ≤ 0x48 → memLoad32 n'.mem (acSlot X.B k) = memLoad32 n.mem (acSlot X.B k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => by rw [acf_slot_add]; exact h34 _ (by omega) (by omega)
  have hmr : maxRoots = 64 := rfl
  have hcl := (acs_decode_docs hd).1
  have hc : (memLoad32 n'.mem (acSlot X.B 0x34C)).toNat = parts.roots.length := by
    rw [hcnt, BitVec.toNat_ofNat]; omega
  have da := fun i (hi : i < parts.roots.length + 2) => acs_doc_at hd hL23 hcnt hl hi
  have r24 : reg n' (24 : Fin 32) = reg n (24 : Fin 32) := KR 24 (by decide)
  refine acs_pin hE ok
    { st := ⟨hpc, rfl, fun _ => rfl⟩
      inv := I'
      img := by
        rw [KR 21 (by decide), KR 25 (by decide), KR 27 (by decide)]
        refine S.img.keep fun k hk => acs_idxWin ok.F K ?_ ?_
        · rcases hk with ⟨a, -⟩ | ⟨a, -⟩ <;> omega
        · rcases hk with ⟨-, a⟩ | ⟨-, a⟩ <;> omega
      tuf := by rw [← S.r24, ← S.r23]; exact hd
      pre := ⟨h9, (ld 0x40 (by decide) (by decide)).trans S.res⟩
      r20 := (KR 20 (by decide)).trans S.r20
      cnt := hcnt
      cntle := hcl
      docs := fun j hj => by
        obtain ⟨d1, d2⟩ := da j (by omega)
        exact ⟨_, _, d1, by rw [r24, ← acs_getD_roots hj]; exact d2⟩
      tgt := by
        obtain ⟨d1, d2⟩ := da parts.roots.length (by omega)
        rw [acs_getD_tg] at d1 d2
        rw [hc, r24]; exact acs_actDoc d1 d2
      tr := by
        obtain ⟨d1, d2⟩ := da (parts.roots.length + 1) (by omega)
        rw [acs_getD_tr] at d1 d2
        rw [hc, r24]; exact acs_actDoc d1 d2
      keys := by rw [h30, S.bf]; exact BitVec.add_comm _ _
      bf := (ld 0x34 (by decide) (by decide)).trans S.bf
      len := (ld 0x38 (by decide) (by decide)).trans S.len
      hL := S.hL
      bundle := by
        refine (memBytes_congr fun j hj => ?_).trans S.bundle
        have hb : acBufLen = 0xB954 := rfl
        have e : (X.Bf + BitVec.ofNat 32 j).toNat = X.Bf.toNat + j := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := ok.bfhi; have := S.hL; omega
        have hs := acs_sep_out (ok.inBf (y := X.Bf + BitVec.ofNat 32 j) (by rw [e]; omega)
          (by rw [e]; have := S.hL; omega))
        rcases hs with hs | hs
        · exact K _ (.inl hs) (.inl (by omega))
        · exact K _ (.inr (by omega)) (.inr (by omega)) }

end C3.RV32.Ac
