import C3BootProofs.Proofs.SvLeafH3

/-!
# `sigstore::verify`: SHA-384 of the leaf's `tbsCertificate`

From offset 0xB56 to 0xDC8, `verify_leaf` writes the SHA-384 digest of the
`tbsCertificate` to offset 0x1020 of the frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

theorem SvKeepL.out {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {c w : Nat}
    (K : SvKeepL B M M' L) (h : ∀ p ∈ L, c + w ≤ p.1 ∨ p.1 + p.2 ≤ c) (hc : c + w ≤ 0x1690) :
    ∀ j, j < w → M' (B + 0x21A0 + BitVec.ofNat 32 (c + j)) = M (B + 0x21A0 + BitVec.ofNat 32 (c + j)) :=
  fun j hj => K _ (by omega) fun p hp => by have := h p hp; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The leaf's digest.** From offset 0xB56 to 0xDC8, with the
`tbsCertificate`'s `len` bytes at `p` and its length in the frame word at
0x8C, `sigstore::verify` writes `sha384` of those bytes to offset 0x1020 of
the frame. -/
theorem sv_lhash {B p : Word} {len : Nat} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem) (SC : SvShaCode n.mem)
    (KS : SvKSep B) (s : St n.mem SV n 0xB56 (reg n)) (rsp : reg n sp = B + 0x21A0) (h9 : reg n 9 = p)
    (h27 : reg n 27 = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (hl : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 len) (hin : SvIn B p len) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' 0xDC8 (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 21, 26, 27] → reg n' q = reg n q) ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 = sha384 (memBytes n.mem p len) ∧
      SvKeepL B n.mem n'.mem [(0x74, 8), (0x420, 0xD0), (0xA20, 0xD0), (0x1020, 0x40), (0x1480, 0x30)] ∧
      (∀ x, SvR B x → n'.mem x = n.mem x) := by
  obtain ⟨n1, c1, s1, sp1, k1, K1, H1, f1⟩ := sv_lh1 F E SC KS s rsp h9 hl hin
  have E1 : SvCode n1.mem := E.fr F f1
  have SC1 : SvShaCode n1.mem := SC.sv F KS f1
  obtain ⟨n2, c2, s2, sp2, k2, v25, v23, v9, K2, H2, f2⟩ := sv_lh2 F E1 SC1 KS s1 sp1 H1
  have E2 : SvCode n2.mem := E1.fr F f2
  have SC2 : SvShaCode n2.mem := SC1.sv F KS f2
  have h27' : reg n2 27 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [k2 27 (by decide), k1 27 (by decide), h27]
  obtain ⟨n3, c3, s3, sp3, k3, v20, v8, v24, w78, w74, K3, f3⟩ := sv_lh3 F E2 s2 sp2 h27' H2
  have E3 : SvCode n3.mem := E2.fr F f3
  have SC3 : SvShaCode n3.mem := SC2.sv F KS f3
  have H3 : SvHasher B n3.mem 0xA20 (memBytes n.mem p len) :=
    H2.same (K3.out (fun q hq => by rw [List.mem_singleton] at hq; subst hq; decide) (by decide))
  obtain ⟨n4, c4, s4, sp4, k4, eq4, K4, f4⟩ := sv_lh4 F E3 SC3 KS s3 sp3 v20
    (by rw [k3 25 (by decide), v25]) (by rw [k3 23 (by decide), v23]) H3
  have E4 : SvCode n4.mem := E3.fr F f4
  have SC4 : SvShaCode n4.mem := SC3.sv F KS f4
  have hml : (memBytes n.mem p len).length = len := memBytes_length _ _ _
  have hlen : len < 2 ^ 32 := by have := hin.lo; omega
  obtain ⟨n5, c5, s5, sp5, k5, hv5, K5, f5⟩ := sv_lh5 (lo := BitVec.ofNat 32 (len / 128)) (pos := len % 128)
    (Nat.mod_lt _ (by decide)) F E4 SC4 KS s4 sp4
    (by rw [k4 27 (by decide), k3 27 (by decide), h27'])
    (by rw [k4 23 (by decide), k3 23 (by decide), v23])
    (by rw [k4 24 (by decide), v24]) (by rw [k4 8 (by decide), v8])
    (by rw [K4.w32 (by decide) (fun q hq => by rw [List.mem_singleton] at hq; subst hq; decide), w74, hml])
    (by rw [K4.w32 (by decide) (fun q hq => by rw [List.mem_singleton] at hq; subst hq; decide), w78, hml])
  have E5 : SvCode n5.mem := E4.fr F f5
  obtain ⟨n6, c6, s6, k6, hb6, K6, f6⟩ := sv_lh6 F E5 s5
    (by rw [k5 9 (by decide), k4 9 (by decide), k3 9 (by decide), v9])
    (by rw [k5 23 (by decide), k4 23 (by decide), k3 23 (by decide), v23])
  have E6 : SvCode n6.mem := E5.fr F f6
  obtain ⟨n7, c7, s7, k7, hb7, K7, f7⟩ := sv_lh7 F E6 s6 (by rw [k6 sp (by decide), sp5])
  have hlo : (BitVec.ofNat 32 (len / 128)).toNat = len / 128 := by rw [BitVec.toNat_ofNat]; omega
  rw [hlo, Nat.div_add_mod] at hv5
  refine ⟨n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), s7,
    by rw [k7 sp (by decide), k6 sp (by decide), sp5], fun q hq => ?_, ?_, ?_,
    fun x hx => by rw [f7 x hx, f6 x hx, f5 x hx, f4 x hx, f3 x hx, f2 x hx, f1 x hx]⟩
  · rw [k7 q (by revert hq; revert q; decide), k6 q (by revert hq; revert q; decide),
      k5 q (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide),
      k3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide),
      k1 q (by revert hq; revert q; decide)]
  · rw [hml] at eq4
    rw [hb7, ← memBytes_take' (by decide : 48 ≤ 64), hb6, hv5, ← eq4, sha384_stream]
  · exact ((((((K1.trans K2).trans K3).trans K4).trans K5).trans K6).trans K7).wider fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end C3.RV32.Sv
