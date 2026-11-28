import C3BootProofs.Proofs.SvDer2
import C3BootProofs.Proofs.IntegerIs
import C3BootProofs.Proofs.DerAlgorithm

/-!
# `sigstore::verify`: calls to `Der::optional`

`Der::optional` stores `Result<Option<Tlv>, Error>` at its result: no
element when the next one has another tag, the element and the reader moved
past it when the tag matches, or an error.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- What `Der::optional` leaves at offset `oc` and in the reader at `dc`. -/
def OptW (M : Word → BitVec 8) (B : Word) (oc dc : Nat) (rp rl : Word) :
    Option (Except DerError DerTlv) → Prop
  | none => M (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧ memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = 0
  | some (.error e) => M (B + 0x21A0 + BitVec.ofNat 32 oc) = 1 ∧
      M (B + 0x21A0 + BitVec.ofNat 32 (oc + 1)) = derErrByte e
  | some (.ok t) => M (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = rp + BitVec.ofNat 32 t.header ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 8)) = BitVec.ofNat 32 t.len ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 12)) = rp ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 16)) = BitVec.ofNat 32 (t.header + t.len) ∧
      M (B + 0x21A0 + BitVec.ofNat 32 (oc + 20)) = BitVec.ofNat 8 t.tag ∧
      DerAdvW M B dc rp rl t

theorem lb1 (B : Word) (c : Nat) (h : c + 1 < 2 ^ 32) : B + BitVec.ofNat 32 c + 1 = B + BitVec.ofNat 32 (c + 1) :=
  frame_lit _ (by simpa using h)
theorem lb4 (B : Word) (c : Nat) (h : c + 4 < 2 ^ 32) : B + BitVec.ofNat 32 c + 4 = B + BitVec.ofNat 32 (c + 4) :=
  frame_lit _ (by simpa using h)
theorem lb8 (B : Word) (c : Nat) (h : c + 8 < 2 ^ 32) : B + BitVec.ofNat 32 c + 8 = B + BitVec.ofNat 32 (c + 8) :=
  frame_lit _ (by simpa using h)
theorem lb12 (B : Word) (c : Nat) (h : c + 12 < 2 ^ 32) :
    B + BitVec.ofNat 32 c + 0xC = B + BitVec.ofNat 32 (c + 12) := frame_lit _ (by simpa using h)
theorem lb16 (B : Word) (c : Nat) (h : c + 16 < 2 ^ 32) :
    B + BitVec.ofNat 32 c + 0x10 = B + BitVec.ofNat 32 (c + 16) := frame_lit _ (by simpa using h)

set_option maxHeartbeats 8000000 in
/-- The words `Der::tlv` leaves at its result `B + c`, and in the reader at
`B + dd`, after a successful read. -/
theorem dtm_readB {M : Word → BitVec 8} {B rp rl : Word} {t : DerTlv} {c dd : Nat} (hc : c % 4 = 0)
    (hdd : dd % 4 = 0) (hcd : c + 0x14 ≤ dd + 8 ∨ dd + 16 ≤ c) (hc2 : c + 0x14 ≤ 0x10000) (hd2 : dd + 16 ≤ 0x10000) :
    memLoad32 (derTlvMem M (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 dd) rp rl (.ok t)) (B + BitVec.ofNat 32 c) =
      rp + BitVec.ofNat 32 t.header ∧
    memLoad32 (derTlvMem M (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 dd) rp rl (.ok t))
      (B + BitVec.ofNat 32 (c + 4)) = BitVec.ofNat 32 t.len ∧
    memLoad32 (derTlvMem M (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 dd) rp rl (.ok t))
      (B + BitVec.ofNat 32 (c + 8)) = rp ∧
    memLoad32 (derTlvMem M (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 dd) rp rl (.ok t))
      (B + BitVec.ofNat 32 (c + 12)) = BitVec.ofNat 32 (t.header + t.len) ∧
    derTlvMem M (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 dd) rp rl (.ok t) (B + BitVec.ofNat 32 (c + 16)) =
      BitVec.ofNat 8 t.tag ∧
    memLoad32 (derTlvMem M (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 dd) rp rl (.ok t))
      (B + BitVec.ofNat 32 (dd + 8)) = rp + BitVec.ofNat 32 (t.header + t.len) ∧
    memLoad32 (derTlvMem M (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 dd) rp rl (.ok t))
      (B + BitVec.ofNat 32 (dd + 12)) = rl - BitVec.ofNat 32 (t.header + t.len) := by
  have ldst : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a % 4 = 0 → e % 4 = 0 → a + 4 ≤ 0x10000 →
      e + 4 ≤ 0x10000 → memLoad32 (memStore32 N (B + BitVec.ofNat 32 a) v) (B + BitVec.ofNat 32 e) =
        if a = e then v else memLoad32 N (B + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 h4 => ld_st_sv h1 h2 h3 h4
  have ld8 : ∀ (N : Word → BitVec 8) (a e : Nat) (v : BitVec 8), a + 1 ≤ 0x10000 → e + 4 ≤ 0x10000 →
      (a < e ∨ e + 4 ≤ a) →
      memLoad32 (memStore8 N (B + BitVec.ofNat 32 a) v) (B + BitVec.ofNat 32 e) = memLoad32 N (B + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 => memLoad32_store8_sep (sepS B (by omega) (by omega) (by omega))
  simp only [derTlvMem]
  rw [lb16 B c (by omega), lb12 B c (by omega), lb8 B c (by omega), lb4 B c (by omega), lb12 B dd (by omega),
    lb8 B dd (by omega), memStore8_same]
  simp (disch := omega) only [ld8, ldst, ite_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp (disch := omega) only [ite_eq_right]) <;> trivial

set_option maxHeartbeats 16000000 in
/-- What `derOptMem` leaves on the frame, seen outside the callee's 0x30 bytes. -/
theorem dom_facts {B : Word} {M M' : Word → BitVec 8} {oc dc : Nat} {rp rl : Word}
    (r : Option (Except DerError DerTlv))
    (ho2 : oc + 0x18 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hs : oc + 0x18 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (f : ∀ x, Sep (B + BitVec.ofNat 32 0x2170) 0x30 x 1 →
      M' x = derOptMem M (B + 0x21A0 + BitVec.ofNat 32 oc) (B + BitVec.ofNat 32 0x2180)
        (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r x) :
    SvKeepL B M M' [(oc, 0x18), (dc + 8, 8)] ∧ OptW M' B oc dc rp rl r ∧ (∀ x, SvR B x → M' x = M x) := by
  -- Everything in B-relative offsets.
  have eo : B + 0x21A0 + BitVec.ofNat 32 oc = B + BitVec.ofNat 32 (0x21A0 + oc) := (sv_base' B oc).symm
  have ed : B + 0x21A0 + BitVec.ofNat 32 dc = B + BitVec.ofNat 32 (0x21A0 + dc) := (sv_base' B dc).symm
  have ee : ∀ e, B + 0x21A0 + BitVec.ofNat 32 e = B + BitVec.ofNat 32 (0x21A0 + e) := fun e => (sv_base' B e).symm
  have st : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a + 4 ≤ 0x2660 → e + 1 ≤ 0x2660 → (a + 4 ≤ e ∨ e + 1 ≤ a) →
      memStore32 N (B + BitVec.ofNat 32 a) v (B + BitVec.ofNat 32 e) = N (B + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore32_get_sep (sepS B (by omega) (by omega) (by omega))
  have st8 : ∀ (N : Word → BitVec 8) (a e : Nat) (v : BitVec 8), a + 1 ≤ 0x2660 → e + 1 ≤ 0x2660 → a ≠ e →
      memStore8 N (B + BitVec.ofNat 32 a) v (B + BitVec.ofNat 32 e) = N (B + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore8_ne (add_ofNat_ne _ (by omega) (by omega) (Ne.symm h))
  have cp : ∀ (N : Word → BitVec 8) (a s e n : Nat), a + n ≤ 0x2660 → e + 1 ≤ 0x2660 → (a + n ≤ e ∨ e + 1 ≤ a) →
      copyBytes N (B + BitVec.ofNat 32 a) (B + BitVec.ofNat 32 s) n (B + BitVec.ofNat 32 e) = N (B + BitVec.ofNat 32 e) :=
    fun N a s e n ha he h => copyBytes_sep (sepS B (by omega) (by omega) (by omega)) (Nat.le_refl _)
  -- `derTlvMem` at the callee's result, at a frame byte.
  have dtm : ∀ (t : DerTlv) e, e + 1 ≤ 0x2660 → 0x21A0 ≤ e → (e + 1 ≤ 0x21A0 + dc + 8 ∨ 0x21A0 + dc + 16 ≤ e) →
      derTlvMem M (B + BitVec.ofNat 32 0x2184) (B + BitVec.ofNat 32 (0x21A0 + dc)) rp rl (.ok t)
        (B + BitVec.ofNat 32 e) = M (B + BitVec.ofNat 32 e) := fun t e he h0 h => by
    simp only [derTlvMem]
    rw [lb16 B 0x2184 (by decide), st8 _ _ e _ (by decide) he (by omega), lb12 B 0x2184 (by decide),
      st _ _ e _ (by decide) he (by omega), lb8 B 0x2184 (by decide), st _ _ e _ (by decide) he (by omega),
      lb4 B 0x2184 (by decide), st _ _ e _ (by decide) he (by omega), st _ _ e _ (by decide) he (by omega),
      lb12 B (0x21A0 + dc) (by omega), st _ _ e _ (by omega) he (by omega), lb8 B (0x21A0 + dc) (by omega),
      st _ _ e _ (by omega) he (by omega)]
  have fS : ∀ e, 0x21A0 ≤ e → e + 1 ≤ 0x2660 → Sep (B + BitVec.ofNat 32 0x2170) 0x30 (B + BitVec.ofNat 32 e) 1 :=
    fun e h1 h2 => sepS B (by omega) (by omega) (by omega)
  have ldS : ∀ e, 0x21A0 ≤ e → e + 4 ≤ 0x2660 → memLoad32 M' (B + BitVec.ofNat 32 e) =
      memLoad32 (derOptMem M (B + BitVec.ofNat 32 (0x21A0 + oc)) (B + BitVec.ofNat 32 0x2180)
        (B + BitVec.ofNat 32 (0x21A0 + dc)) rp rl r) (B + BitVec.ofNat 32 e) := fun e h1 h2 =>
    memLoad32_congr fun j hj => by rw [add_ofNat_assoc, f _ (fS _ (by omega) (by omega)), eo, ed]
  have ldst : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a % 4 = 0 → e % 4 = 0 → a + 4 ≤ 0x2660 →
      e + 4 ≤ 0x2660 → memLoad32 (memStore32 N (B + BitVec.ofNat 32 a) v) (B + BitVec.ofNat 32 e) =
        if a = e then v else memLoad32 N (B + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 h4 => ld_st_sv h1 h2 (by omega) (by omega)
  have ld8 : ∀ (N : Word → BitVec 8) (a e : Nat) (v : BitVec 8), a + 1 ≤ 0x2660 → e + 4 ≤ 0x2660 → (a < e ∨ e + 4 ≤ a) →
      memLoad32 (memStore8 N (B + BitVec.ofNat 32 a) v) (B + BitVec.ofNat 32 e) = memLoad32 N (B + BitVec.ofNat 32 e) :=
    fun N a e v h1 h2 h3 => memLoad32_store8_sep (sepS B (by omega) (by omega) (by omega))
  have F4 : B + BitVec.ofNat 32 0x2180 + 4 = B + BitVec.ofNat 32 0x2184 := lb4 B 0x2180 (by decide)
  refine ⟨fun e he hL => ?_, ?_, fun x hx => ?_⟩
  · have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h1 h2
    rw [ee, f _ (fS _ (by omega) (by omega)), eo, ed]
    cases r with
    | none => simp only [derOptMem]; rw [lb4 B (0x21A0 + oc) (by omega), st _ _ _ _ (by omega) (by omega) (by omega),
        st8 _ _ _ _ (by omega) (by omega) (by omega)]
    | some r =>
      cases r with
      | error er => simp only [derOptMem]; rw [st8 _ _ _ _ (by omega) (by omega) (by omega), lb1 B (0x21A0 + oc) (by omega),
          st8 _ _ _ _ (by omega) (by omega) (by omega)]
      | ok t => simp only [derOptMem]; rw [st8 _ _ _ _ (by omega) (by omega) (by omega), F4, lb4 B (0x21A0 + oc) (by omega),
          cp _ _ _ _ _ (by omega) (by omega) (by omega), dtm t _ (by omega) (by omega) (by omega)]
  · cases r with
    | none =>
      refine ⟨?_, ?_⟩
      · rw [ee, f _ (fS _ (by omega) (by omega)), eo, ed]; simp only [derOptMem]
        rw [lb4 B (0x21A0 + oc) (by omega), st _ _ _ _ (by omega) (by omega) (by omega), memStore8_same]
      · rw [ee, ldS _ (by omega) (by omega)]; simp only [derOptMem]
        rw [lb4 B (0x21A0 + oc) (by omega), show 0x21A0 + (oc + 4) = 0x21A0 + oc + 4 by omega, memLoad32_store32_same]
    | some r =>
      cases r with
      | error er =>
        refine ⟨?_, ?_⟩
        · rw [ee, f _ (fS _ (by omega) (by omega)), eo, ed]; simp only [derOptMem]; rw [memStore8_same]
        · rw [ee, f _ (fS _ (by omega) (by omega)), eo, ed]; simp only [derOptMem]
          rw [st8 _ _ _ _ (by omega) (by omega) (by omega), lb1 B (0x21A0 + oc) (by omega),
            show 0x21A0 + (oc + 1) = 0x21A0 + oc + 1 by omega, memStore8_same]
      | ok t =>
        obtain ⟨x0, x4, x8, x12, x16, xd8, xd12⟩ := dtm_readB (M := M) (B := B) (rp := rp) (rl := rl) (t := t)
          (c := 0x2184) (dd := 0x21A0 + dc) (by decide) (by omega) (by omega) (by decide) (by omega)
        have rd : ∀ k, k + 4 ≤ 0x14 → memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 (oc + 4 + k)) =
            memLoad32 (derTlvMem M (B + BitVec.ofNat 32 0x2184) (B + BitVec.ofNat 32 (0x21A0 + dc)) rp rl (.ok t))
              (B + BitVec.ofNat 32 (0x2184 + k)) := fun k hk => by
          rw [ee, ldS _ (by omega) (by omega)]; simp only [derOptMem]
          rw [ld8 _ _ _ _ (by omega) (by omega) (by omega),
            show B + BitVec.ofNat 32 (0x21A0 + (oc + 4 + k)) = B + BitVec.ofNat 32 (0x21A0 + oc) + 4 + BitVec.ofNat 32 k by
              sv_addr, F4, cp_word hk (by decide), add_ofNat_assoc]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [ee, f _ (fS _ (by omega) (by omega)), eo, ed]; simp only [derOptMem]; rw [memStore8_same]
        · rw [show oc + 4 = oc + 4 + 0 from rfl, rd 0 (by decide)]; exact x0
        · rw [show oc + 8 = oc + 4 + 4 by omega, rd 4 (by decide)]; exact x4
        · rw [show oc + 12 = oc + 4 + 8 by omega, rd 8 (by decide)]; exact x8
        · rw [show oc + 16 = oc + 4 + 12 by omega, rd 12 (by decide)]; exact x12
        · rw [ee, f _ (fS _ (by omega) (by omega)), eo, ed]; simp only [derOptMem]
          rw [st8 _ _ _ _ (by omega) (by omega) (by omega),
            show B + BitVec.ofNat 32 (0x21A0 + (oc + 20)) = B + BitVec.ofNat 32 (0x21A0 + oc) + 4 + BitVec.ofNat 32 0x10 by
              sv_addr, F4, cp_at (by decide) (by decide), add_ofNat_assoc]
          exact x16
        · rw [ee, ldS _ (by omega) (by omega)]; simp only [derOptMem]
          rw [ld8 _ _ _ _ (by omega) (by omega) (by omega), F4,
            cp_word_out (by rw [lb4 B (0x21A0 + oc) (by omega)]; exact sepS B (by omega) (by omega) (by omega)),
            show 0x21A0 + (dc + 8) = 0x21A0 + dc + 8 by omega]
          exact xd8
        · rw [ee, ldS _ (by omega) (by omega)]; simp only [derOptMem]
          rw [ld8 _ _ _ _ (by omega) (by omega) (by omega), F4,
            cp_word_out (by rw [lb4 B (0x21A0 + oc) (by omega)]; exact sepS B (by omega) (by omega) (by omega)),
            show 0x21A0 + (dc + 12) = 0x21A0 + dc + 12 by omega]
          exact xd12
  · have hxF : Sep (B + BitVec.ofNat 32 0x2170) 0x30 x 1 := by
      have := svR_lo (k := 0x30) hx (by decide) (by decide)
      rwa [sv_lo B 0x30 (by decide)] at this
    have hx' : ∀ c n, 0x21A0 ≤ c → c + n ≤ 0x2660 → Sep (B + BitVec.ofNat 32 c) n x 1 := fun c n h1 h2 => by
      have := svR_hi (c := c - 0x21A0) (l := n) hx (by omega)
      rwa [← sv_base', show 0x21A0 + (c - 0x21A0) = c by omega] at this
    have hxL : ∀ c n, 0x2170 ≤ c → c + n ≤ 0x21A0 → Sep (B + BitVec.ofNat 32 c) n x 1 := fun c n h1 h2 => by
      have := hxF.sub (c := c - 0x2170) (l := n) (by omega)
      rwa [add_ofNat_assoc, show 0x2170 + (c - 0x2170) = c by omega] at this
    rw [f x hxF, eo, ed]
    cases r with
    | none => simp only [derOptMem]; rw [lb4 B (0x21A0 + oc) (by omega), memStore32_get_sep (hx' _ 4 (by omega) (by omega)),
        memStore8_ne (sep1_ne (hx' _ 1 (by omega) (by omega)))]
    | some r =>
      cases r with
      | error er => simp only [derOptMem]; rw [memStore8_ne (sep1_ne (hx' _ 1 (by omega) (by omega))), lb1 B (0x21A0 + oc) (by omega),
          memStore8_ne (sep1_ne (hx' _ 1 (by omega) (by omega)))]
      | ok t =>
        simp only [derOptMem]
        rw [memStore8_ne (sep1_ne (hx' _ 1 (by omega) (by omega))), F4, lb4 B (0x21A0 + oc) (by omega),
          copyBytes_sep (hx' _ 0x14 (by omega) (by omega)) (Nat.le_refl _)]
        simp only [derTlvMem]
        rw [lb16 B 0x2184 (by decide), memStore8_ne (sep1_ne (hxL _ 1 (by decide) (by decide))),
          lb12 B 0x2184 (by decide), memStore32_get_sep (hxL _ 4 (by decide) (by decide)),
          lb8 B 0x2184 (by decide), memStore32_get_sep (hxL _ 4 (by decide) (by decide)),
          lb4 B 0x2184 (by decide), memStore32_get_sep (hxL _ 4 (by decide) (by decide)),
          memStore32_get_sep (hxL _ 4 (by decide) (by decide)),
          lb12 B (0x21A0 + dc) (by omega), memStore32_get_sep (hx' _ 4 (by omega) (by omega)),
          lb8 B (0x21A0 + dc) (by omega), memStore32_get_sep (hx' _ 4 (by omega) (by omega))]

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::optional`** with tag `tag`, the result at offset `oc`
and the reader at offset `dc`. -/
theorem sv_optF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {oc dc tag : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derOptionalAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc) (ha2 : reg n a2 = BitVec.ofNat 32 tag) (htag : tag < 256)
    (ho2 : oc + 0x18 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hs : oc + 0x18 ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q, optKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 0x18), (dc + 8, 8)] ∧
      OptW n'.mem B oc dc rp rl (derOptRes tag (memBytes M rp rl.toNat)) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : C3.RV32.OptEnv M (BitVec.ofNat 32 derOptionalAddress) (B + 0x21A0)
      (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 dc) := by
    refine ⟨by decide, C.derOptional, C.tlv, C.K.stub, C.K.body, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) ho3
    · exact sv_al F (by omega) hd3
    · rw [sv_at F _ (by omega)]; omega
    · rw [sv_sp30]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp30]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp30]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [sv_sp30]; exact F.sepHi (by decide) (by decide) (by decide)
    · rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide)
    · rw [sv_sp30, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp30, d8, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [d8, ← sv_base', ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp30, d8, d12, hrp, hrl]; exact hin.sepLo (by decide)
    · rw [d8, hrp]; exact hin.pos
    · rw [d8, d12, hrp, hrl]; exact hin.fit
  obtain ⟨n2, c2, pc2, sp2, k2, f2⟩ := derOptional_correct n1 (tag := tag) (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]) htag (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp30, show B + 0x21A0 + 0xFFFFFFE0 = B + BitVec.ofNat 32 0x2180 from sv_sp20 B]
    at f2
  obtain ⟨K, R, fr⟩ := dom_facts _ ho2 ho3 hd2 hd3 hs f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr], K, R, fr⟩

set_option maxHeartbeats 8000000 in
/-- What `derAdvance` leaves on the frame, seen outside a callee frame `kf`
bytes below the base. -/
theorem dad_facts {B : Word} {M M' : Word → BitVec 8} {dc kf : Nat} {rp rl : Word}
    (r : Except DerError DerTlv) (hkf : kf ≤ 0x200) (hkf0 : 0 < kf) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (f : ∀ x, Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf x 1 →
      M' x = derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl r x) :
    SvKeepL B M M' [(dc + 8, 8)] ∧ (∀ t, r = .ok t → DerAdvW M' B dc rp rl t) ∧ (∀ x, SvR B x → M' x = M x) := by
  have fS : ∀ e, e + 1 ≤ 0x4C0 → Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf (B + 0x21A0 + BitVec.ofNat 32 e) 1 :=
    fun e he => by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega)
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have st : ∀ (N : Word → BitVec 8) (a e : Nat) (v : Word), a + 4 ≤ 0x4C0 → e + 1 ≤ 0x4C0 → (a + 4 ≤ e ∨ e + 1 ≤ a) →
      memStore32 N (B + 0x21A0 + BitVec.ofNat 32 a) v (B + 0x21A0 + BitVec.ofNat 32 e) =
        N (B + 0x21A0 + BitVec.ofNat 32 e) :=
    fun N a e v ha he h => memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  refine ⟨fun e he hL => ?_, fun t ht => ?_, fun x hx => ?_⟩
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    rw [f _ (fS e he)]
    cases r with
    | error _ => rfl
    | ok t => simp only [derAdvance]; rw [d12, st _ (dc + 12) e _ (by omega) he (by omega), d8,
        st _ (dc + 8) e _ (by omega) he (by omega)]
  · subst ht
    have ld : ∀ e, e + 4 ≤ 0x4C0 → memLoad32 M' (B + 0x21A0 + BitVec.ofNat 32 e) =
        memLoad32 (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) rp rl (.ok t)) (B + 0x21A0 + BitVec.ofNat 32 e) :=
      fun e he => memLoad32_congr fun j hj => f _ (by rw [add_ofNat_assoc]; exact fS _ (by omega))
    refine ⟨?_, ?_⟩
    · rw [ld _ (by omega)]; simp only [derAdvance]
      rw [d12, d8, ld_st_sv (by omega) (by omega) (by omega) (by omega), ite_eq_right (by omega),
        memLoad32_store32_same]
    · rw [ld _ (by omega)]; simp only [derAdvance]; rw [d12, memLoad32_store32_same]
  · have hxF : Sep (B + BitVec.ofNat 32 (0x21A0 - kf)) kf x 1 := by
      have := svR_lo (k := kf) hx (by omega) hkf0
      rwa [sv_lo B kf (by omega)] at this
    rw [f x hxF]
    cases r with
    | error _ => rfl
    | ok t => simp only [derAdvance]; rw [d12, memStore32_get_sep (svR_hi hx (by omega)), d8,
        memStore32_get_sep (svR_hi hx (by omega))]

theorem sv_sp40 (B : Word) : B + 0x21A0 + 0xFFFFFFC0 = B + BitVec.ofNat 32 0x2160 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **A call to `Der::integer_is`** with the reader at offset `dc` and the
expected value in `a1`. -/
theorem sv_iiF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o rp rl : Word} {dc : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derIntegerIsAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = rp)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = rl)
    (hin : SvIn B rp rl.toNat) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(dc + 8, 8)] ∧
      (∀ t, derElement 2 (memBytes M rp rl.toNat) = .ok t → DerAdvW n'.mem B dc rp rl t) ∧
      (match derIntIsOf M (memBytes M rp rl.toNat) rp (derElement 2 (memBytes M rp rl.toNat))
          ((reg n a1).extractLsb' 0 8) with
        | .error b => reg n' a0 = 1 ∧ (reg n' a1).extractLsb' 0 8 = b
        | .ok v => reg n' a0 = 0 ∧ reg n' a1 = if v then 1 else 0) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : IIEnv M (BitVec.ofNat 32 derIntegerIsAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 dc) := by
    refine ⟨by decide, C.derIntegerIs, C.derInteger, C.elem, C.tlv, C.sliceEq, C.equalSameLength, C.memcmp,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) hd3
    all_goals first
      | (rw [sv_sp40]; exact F.sepHi (by decide) (by decide) (by decide))
      | (rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
      | (rw [d8, sv_sp40, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      | (rw [sv_sp40, d8, d12, hrp, hrl]; exact hin.sepLo (by decide))
      | (rw [d8, d12, hrp, hrl, ← sv_base']; exact (hin.sepLo (by omega)).symm)
      | (rw [d8, hrp]; exact hin.pos)
      | (rw [d8, d12, hrp, hrl]; exact hin.fit)
  obtain ⟨n2, c2, pc2, sp2, k2, f2, R⟩ := derIntegerIs_correct n1 (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, d8, d12, hrp, hrl, sv_sp40] at f2
  rw [mem1, d8, d12, hrp, hrl, r1 a1 (by decide)] at R
  obtain ⟨K, A, fr⟩ := dad_facts (kf := 0x40) _ (by decide) (by decide) hd2 hd3 f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], K, A, R, fr⟩

theorem sv_sp70 (B : Word) : B + 0x21A0 + 0xFFFFFF90 = B + BitVec.ofNat 32 0x2130 := by
  rw [BitVec.add_assoc]; rfl

theorem lit24 (S : Word) (c : Nat) (hc : c + 24 < 2 ^ 32) :
    S + BitVec.ofNat 32 c + 0x18 = S + BitVec.ofNat 32 (c + 24) := frame_lit _ (by simpa using hc)

/-- What `Der::algorithm` leaves at offset `oc`. -/
def AlgW (M : Word → BitVec 8) (B : Word) (oc : Nat) : Except (BitVec 8) ((Word × Nat) × Option (Word × DerTlv)) → Prop
  | .error b => memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧ M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = b
  | .ok ((op, ol), none) => memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = op ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = BitVec.ofNat 32 ol ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 8)) = 0
  | .ok ((op, ol), some (rp, u)) => memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = op ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = BitVec.ofNat 32 ol ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 8)) = rp + BitVec.ofNat 32 u.header ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 12)) = BitVec.ofNat 32 u.len ∧
      M (B + 0x21A0 + BitVec.ofNat 32 (oc + 24)) = BitVec.ofNat 8 u.tag

set_option maxHeartbeats 16000000 in
/-- **A call to `Der::algorithm`** with the result at offset `oc` and the
reader at offset `dc`, whose unread bytes are `n` bytes at `p`. -/
theorem sv_algF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p : Word} {oc dc nl : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 derAlgorithmAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 dc)
    (ho2 : oc + 0x1C ≤ 0x4C0) (ho3 : oc % 4 = 0) (hd2 : dc + 16 ≤ 0x4C0) (hd3 : dc % 4 = 0)
    (hs : oc + 0x1C ≤ dc + 8 ∨ dc + 16 ≤ oc)
    (hrp : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 8)) = p)
    (hrl : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (dc + 12)) = BitVec.ofNat 32 nl)
    (hin : SvIn B p nl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 0x1C), (dc + 8, 8)] ∧
      (∀ t, derElement 0x30 (memBytes M p nl) = .ok t → DerAdvW n'.mem B dc p (BitVec.ofNat 32 nl) t) ∧
      AlgW n'.mem B oc (derAlgOf M p nl) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have d8 := lit8 (B + 0x21A0) dc (by omega)
  have d12 := lit12 (B + 0x21A0) dc (by omega)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have env : AlgEnv M (BitVec.ofNat 32 derAlgorithmAddress) (B + 0x21A0) (B + 0x21A0 + BitVec.ofNat 32 oc)
      (B + 0x21A0 + BitVec.ofNat 32 dc) p nl := by
    refine ⟨by decide, C.derAlgorithm, C.seq, C.nest, C.elem, C.tlv, C.derOid, C.K.stub, C.K.body,
      ?_, ?_, ?_, ?_, ?_, by rw [d8, hrp], by rw [d12, hrl], hin.pos, hin.fit,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hS]; omega
    · rw [hS]; omega
    · exact sv_al F (by omega) ho3
    · rw [sv_at F _ (by omega)]; omega
    · exact sv_al F (by omega) hd3
    iterate 8 (· rw [sv_sp70]; exact F.sepHi (by decide) (by decide) (by decide))
    iterate 2 (· rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
    · rw [sv_sp70, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    iterate 7 (· rw [d8, ← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
    · rw [d8, sv_sp70, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [d8, ← sv_base', ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp70]; exact hin.sepLo (by decide)
    · rw [d8, ← sv_base']; exact (hin.sepLo (by omega))
  obtain ⟨n2, c2, pc2, sp2, k2, f2, R⟩ := derAlgorithm_correct n1 (by rw [mem1]; exact env)
    pc1 (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1, sv_sp70] at f2
  rw [mem1] at R
  have o4 := lit4 (B + 0x21A0) oc (by omega)
  have o8 := lit8 (B + 0x21A0) oc (by omega)
  have f2' : ∀ x, Sep (B + BitVec.ofNat 32 (0x21A0 - 0x70)) 0x70 x 1 → Sep (B + 0x21A0 + BitVec.ofNat 32 oc) 0x1C x 1 →
      n2.mem x = derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) p (BitVec.ofNat 32 nl) (derElement 0x30 (memBytes M p nl)) x :=
    fun x h1 h2 => f2 x h1 h2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], ?_, ?_, ?_, ?_⟩
  · intro e he hL
    have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h1 h2
    rw [f2' _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))]
    cases derElement 0x30 (memBytes M p nl) with
    | error _ => rfl
    | ok t => simp only [derAdvance]; rw [d12, memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)),
        d8, memStore32_get_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega))]
  · intro t ht
    have ld : ∀ e, e + 4 ≤ 0x4C0 → (e + 4 ≤ oc ∨ oc + 0x1C ≤ e) → memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 e) =
        memLoad32 (derAdvance M (B + 0x21A0 + BitVec.ofNat 32 dc) p (BitVec.ofNat 32 nl) (.ok t))
          (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h => by
      rw [← ht]; exact memLoad32_congr fun j hj => f2' _
        (by rw [add_ofNat_assoc, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
        (by rw [add_ofNat_assoc]; exact sepS (B + 0x21A0) (by omega) (by omega) (by omega))
    refine ⟨?_, ?_⟩
    · rw [ld _ (by omega) (by omega)]; simp only [derAdvance]
      rw [d12, d8, ld_st_sv (by omega) (by omega) (by omega) (by omega), ite_eq_right (by omega),
        memLoad32_store32_same]
    · rw [ld _ (by omega) (by omega)]; simp only [derAdvance]; rw [d12, memLoad32_store32_same]
  · revert R
    cases derAlgOf M p nl with
    | error b => intro R; exact ⟨R.1, by rw [← o4]; exact R.2⟩
    | ok v =>
      obtain ⟨⟨op, ol⟩, w⟩ := v
      cases w with
      | none => intro R; exact ⟨R.1, by rw [← o4]; exact R.2.1, by rw [← o8]; exact R.2.2⟩
      | some w =>
        obtain ⟨rp, u⟩ := w; intro R
        exact ⟨R.1, by rw [← o4]; exact R.2.1, by rw [← o8]; exact R.2.2.1,
          by rw [← lit12 (B + 0x21A0) oc (by omega)]; exact R.2.2.2.1,
          by rw [← lit24 (B + 0x21A0) oc (by omega)]; exact R.2.2.2.2.2.2⟩
  · intro x hx
    have hxF : Sep (B + BitVec.ofNat 32 (0x21A0 - 0x70)) 0x70 x 1 := by
      have := svR_lo (k := 0x70) hx (by decide) (by decide)
      rwa [sv_lo B 0x70 (by decide)] at this
    rw [f2' x hxF (svR_hi hx ho2)]
    cases derElement 0x30 (memBytes M p nl) with
    | error _ => rfl
    | ok t => simp only [derAdvance]; rw [d12, memStore32_get_sep (svR_hi hx (by omega)), d8,
        memStore32_get_sep (svR_hi hx (by omega))]

end C3.RV32.Sv
