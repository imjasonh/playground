import C3BootProofs.Spec.Formats

/-!
# Facts about the image header

An accepted header's segments lie inside the signed image, no two overlap,
and each flash segment is whole pages. The cache maps flash in whole pages,
so every byte it maps is a signed byte of the image.
-/

namespace C3

/-- An accepted header repeats the manifest's image length, every segment
passes the per-segment rules, and no two segments overlap. -/
theorem decodeImageHeader_ok {bytes : Bytes} {n : Nat} {h : ImageHeader}
    (hd : decodeImageHeader bytes n = some h) :
    h.imageLength = n ∧ (∀ s ∈ h.segments, segmentOk n s = true) ∧
      noOverlaps h.segments = true := by
  unfold decodeImageHeader at hd
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, require_eq_some, Option.pure_def,
    Option.some.injEq, exists_const] at hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hall, _, hov, _, rfl⟩ := hd
  refine ⟨rfl, ?_, hov⟩
  intro s hs
  exact List.all_eq_true.mp hall s hs

/-- Every segment of an accepted header ends inside the signed image. -/
theorem segment_in_image {bytes : Bytes} {n : Nat} {h : ImageHeader}
    (hd : decodeImageHeader bytes n = some h) {s : Segment} (hs : s ∈ h.segments) :
    s.offset + s.length ≤ n := by
  have hok := (decodeImageHeader_ok hd).2.1 s hs
  unfold segmentOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  omega

/-- For a flash segment of an accepted header, each 64 KiB page the cache
maps, the `k`-th from the segment's start for `k` below its page count, ends
inside the signed image. -/
theorem mapped_pages_signed {bytes : Bytes} {n : Nat} {h : ImageHeader}
    (hd : decodeImageHeader bytes n = some h) {s : Segment} (hs : s ∈ h.segments)
    (hflash : s.kind.isFlash = true) {k : Nat} (hk : k < s.length / flashPage) :
    s.offset + (k + 1) * flashPage ≤ n := by
  have hok := (decodeImageHeader_ok hd).2.1 s hs
  unfold segmentOk at hok
  rw [hflash] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, ite_true, beq_iff_eq] at hok
  unfold flashPage at *
  omega

end C3
