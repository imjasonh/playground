import C3BootProofs.Spec.Formats

/-!
# The image header decoder reads at most 0x114 bytes

`tuf_slot::accept_slot` gives `image::parse` only the image's first 0x114
bytes: the 20-byte fixed header and at most 16 segments of 16 bytes each. The
spec decodes the whole image. `decodeImageHeader_take` says that the decoder
never reads past those bytes, so the two decide the same.
-/

namespace C3

theorem aci_take_take (n : Nat) : ∀ (k : Nat) (bs : Bytes), (bs.take (n + k)).take k = bs.take k
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: t => congrArg (_ :: ·) (aci_take_take n k t)

theorem aci_drop_take (n : Nat) : ∀ (k : Nat) (bs : Bytes), (bs.take (n + k)).drop k = (bs.drop k).take n
  | 0, _ => rfl
  | _ + 1, [] => by rw [List.take_nil, List.drop_nil, List.take_nil]
  | k + 1, _ :: t => aci_drop_take n k t

theorem aci_lt_take (n : Nat) : ∀ (k : Nat) (bs : Bytes), (bs.take (n + k)).length < k ↔ bs.length < k
  | 0, _ => ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.not_lt_zero _)⟩
  | _ + 1, [] => by rw [List.take_nil]
  | k + 1, _ :: t => by
    show (t.take (n + k)).length + 1 < k + 1 ↔ t.length + 1 < k + 1
    rw [Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_right]
    exact aci_lt_take n k t

theorem aci_le_take (n k : Nat) (bs : Bytes) : k ≤ (bs.take (n + k)).length ↔ k ≤ bs.length := by
  rw [← Nat.not_lt, ← Nat.not_lt, aci_lt_take]

theorem aci_readU8_take (bs : Bytes) (n : Nat) :
    readU8 (bs.take (n + 1)) = (readU8 bs).map fun p => (p.1, p.2.take n) := by
  cases bs <;> rfl

theorem aci_readU16_take (bs : Bytes) (n : Nat) :
    readU16 (bs.take (n + 2)) = (readU16 bs).map fun p => (p.1, p.2.take n) := by
  match bs with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem aci_readU32_take (bs : Bytes) (n : Nat) :
    readU32 (bs.take (n + 4)) = (readU32 bs).map fun p => (p.1, p.2.take n) := by
  match bs with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ => rfl

theorem aci_readZeros_take (k : Nat) (bs : Bytes) (n : Nat) :
    readZeros k (bs.take (n + k)) = (readZeros k bs).map (·.take n) := by
  unfold readZeros
  have hl := aci_lt_take n k bs
  have ht := aci_take_take n k bs
  have hd := aci_drop_take n k bs
  by_cases h : bs.length < k
  · rw [ite_eq_left (hl.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun e => h (hl.mp e)), ite_eq_right h, ht, hd]
    cases (bs.take k).all (· == 0) <;> rfl

theorem aci_readExpect_take (want bs : Bytes) (n : Nat) :
    readExpect want (bs.take (n + want.length)) = (readExpect want bs).map (·.take n) := by
  unfold readExpect
  have ht := aci_take_take n want.length bs
  have hd := aci_drop_take n want.length bs
  have hl : decide (want.length ≤ (bs.take (n + want.length)).length) = decide (want.length ≤ bs.length) :=
    decide_eq_decide.mpr (aci_le_take n want.length bs)
  rw [ht, hd, hl]
  split <;> rfl

theorem aci_readHeader_take (magic bs : Bytes) (hm : magic.length = 4) (n : Nat) :
    readHeader magic (bs.take (n + 6)) = (readHeader magic bs).map (·.take n) := by
  unfold readHeader
  rw [show n + 6 = (n + 2) + magic.length by omega, aci_readExpect_take]
  cases readExpect magic bs with
  | none => rfl
  | some r =>
    show (readU16 (r.take (n + 2)) >>= _) = Option.map _ (readU16 r >>= _)
    rw [aci_readU16_take]
    cases readU16 r with
    | none => rfl
    | some p =>
      show (require (p.1 == 1) >>= fun _ => pure (p.2.take n)) = Option.map _ (require (p.1 == 1) >>= _)
      cases p.1 == 1 <;> rfl

theorem aci_readSegment_take (bs : Bytes) (n : Nat) :
    readSegment (bs.take (n + 16)) = (readSegment bs).map fun p => (p.1, p.2.take n) := by
  unfold readSegment
  rw [show n + 16 = (n + 15) + 1 from rfl, aci_readU8_take]
  cases readU8 bs with
  | none => rfl
  | some p =>
    obtain ⟨b, r⟩ := p
    show (SegmentKind.ofByte b >>= _) = Option.map _ (SegmentKind.ofByte b >>= _)
    cases SegmentKind.ofByte b with
    | none => rfl
    | some kind =>
      show (readZeros 3 (r.take (n + 12 + 3)) >>= _) = Option.map _ (readZeros 3 r >>= _)
      rw [aci_readZeros_take]
      cases readZeros 3 r with
      | none => rfl
      | some r1 =>
        show (readU32 (r1.take (n + 8 + 4)) >>= _) = Option.map _ (readU32 r1 >>= _)
        rw [aci_readU32_take]
        cases readU32 r1 with
        | none => rfl
        | some p2 =>
          show (readU32 (p2.2.take (n + 4 + 4)) >>= _) = Option.map _ (readU32 p2.2 >>= _)
          rw [aci_readU32_take]
          cases readU32 p2.2 with
          | none => rfl
          | some p3 =>
            show (readU32 (p3.2.take (n + 4)) >>= _) = Option.map _ (readU32 p3.2 >>= _)
            rw [aci_readU32_take]
            cases readU32 p3.2 <;> rfl

theorem aci_readSegments_take : ∀ (c : Nat) (bs : Bytes) (n : Nat),
    readSegments c (bs.take (n + 16 * c)) = readSegments c bs
  | 0, _, _ => rfl
  | c + 1, bs, n => by
    unfold readSegments
    rw [show n + 16 * (c + 1) = (n + 16 * c) + 16 by omega, aci_readSegment_take]
    cases readSegment bs with
    | none => rfl
    | some p =>
      show (readSegments c (p.2.take (n + 16 * c)) >>= _) = (readSegments c p.2 >>= _)
      rw [aci_readSegments_take c p.2 n]

/-- **The header decoder reads at most the image's first 0x114 bytes.** -/
theorem decodeImageHeader_take (bs : Bytes) (L : Nat) :
    decodeImageHeader (bs.take 0x114) L = decodeImageHeader bs L := by
  unfold decodeImageHeader
  rw [show (0x114 : Nat) = 0x10E + 6 from rfl, aci_readHeader_take _ _ rfl]
  cases readHeader magicImage bs with
  | none => rfl
  | some r =>
    show (readU16 (r.take (0x10C + 2)) >>= _) = (readU16 r >>= _)
    rw [aci_readU16_take]
    cases readU16 r with
    | none => rfl
    | some p =>
      obtain ⟨chip, r⟩ := p
      show (require (chip == 5) >>= _) = (require (chip == 5) >>= _)
      cases chip == 5 with
      | false => rfl
      | true =>
        show (readU8 (r.take (0x10B + 1)) >>= _) = (readU8 r >>= _)
        rw [aci_readU8_take]
        cases readU8 r with
        | none => rfl
        | some p =>
          obtain ⟨sv, r⟩ := p
          show (require (decide (sv ≤ 16)) >>= _) = (require (decide (sv ≤ 16)) >>= _)
          cases decide (sv ≤ 16) with
          | false => rfl
          | true =>
            show (readU8 (r.take (0x10A + 1)) >>= _) = (readU8 r >>= _)
            rw [aci_readU8_take]
            cases readU8 r with
            | none => rfl
            | some p =>
              obtain ⟨count, r⟩ := p
              show (require (decide (0 < count) && decide (count ≤ 16)) >>= _) =
                (require (decide (0 < count) && decide (count ≤ 16)) >>= _)
              by_cases hc : (decide (0 < count) && decide (count ≤ 16)) = true
              · rw [hc]
                have hc16 : count ≤ 16 := by simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.2
                show (readZeros 2 (r.take (0x108 + 2)) >>= _) = (readZeros 2 r >>= _)
                rw [aci_readZeros_take]
                cases readZeros 2 r with
                | none => rfl
                | some r =>
                  show (readU32 (r.take (0x104 + 4)) >>= _) = (readU32 r >>= _)
                  rw [aci_readU32_take]
                  cases readU32 r with
                  | none => rfl
                  | some p =>
                    obtain ⟨entry, r⟩ := p
                    show (readU32 (r.take (0x100 + 4)) >>= _) = (readU32 r >>= _)
                    rw [aci_readU32_take]
                    cases readU32 r with
                    | none => rfl
                    | some p =>
                      obtain ⟨length, r⟩ := p
                      show (require (length == L) >>= fun _ => readSegments count (r.take 0x100) >>= _) =
                        (require (length == L) >>= fun _ => readSegments count r >>= _)
                      rw [show (0x100 : Nat) = (0x100 - 16 * count) + 16 * count by omega,
                        aci_readSegments_take]
              · rw [Bool.not_eq_true] at hc
                rw [hc]; rfl

end C3
