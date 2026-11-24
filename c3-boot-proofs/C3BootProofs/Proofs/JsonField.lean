import C3BootProofs.Proofs.JsonGet

/-!
# `Value::field`, as compiled

`field(key)` calls `get(key)` and turns `Ok(None)` into the error byte
`0x21` (`TufError::Schema`). Its result has the layout `FieldRes`
describes: the value's pointer at `out` and its length at `out + 4`, or a
zero word at `out` and the error byte at `out + 4`. A value's pointer is
never zero, because the document at `p` doesn't wrap and `p` isn't zero.

The function keeps two registers in a 32-byte frame, and `get` uses 228
more bytes, so the stack region is the 260 bytes below `sp`.
`jsonField_correct` is the contract.
-/

namespace C3.Json

/-- `Value::field(key)` on the value `d`: the value's start and length, or
the error byte. -/
def objField (d key : Bytes) : Except Nat (Nat × Nat) :=
  match objGet d key with
  | .error e => .error e
  | .ok none => .error 0x21
  | .ok (some x) => .ok x

theorem getFrom_val {d key : Bytes} {vp vl : Nat} :
    ∀ k pos, getFrom d key k pos = some (some (vp, vl)) → vp < d.length ∧ vp + vl ≤ d.length
  | 0, _, h => by cases h
  | k + 1, pos, h => by
    simp only [getFrom] at h
    cases hn : nextMember d pos with
    | none => rw [hn] at h; cases h
    | some r =>
      cases r with
      | none => rw [hn] at h; cases h
      | some t =>
        obtain ⟨kp, kl, vp', vl', a⟩ := t
        rw [hn] at h
        dsimp only at h
        split at h
        · cases h
          have := nextMember_lt hn
          exact ⟨this.2.2.2.2.1, this.2.2.2.2.2⟩
        · exact getFrom_val k a h

/-- A value that `get` finds starts inside the document and ends by its end. -/
theorem objGet_val {d key : Bytes} {vp vl : Nat} (h : objGet d key = .ok (some (vp, vl))) :
    vp < d.length ∧ vp + vl ≤ d.length := by
  unfold objGet at h
  split at h
  · cases h
  · unfold getOut at h
    split at h
    · cases h
    · rename_i r hr
      cases h
      exact getFrom_val _ _ hr

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

theorem fd_at_0 : fetchRel jsonFieldCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem fd_at_2 : fetchRel jsonFieldCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem fd_at_4 : fetchRel jsonFieldCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem fd_at_6 : fetchRel jsonFieldCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem fd_at_8 : fetchRel jsonFieldCode 0x8 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem fd_at_a : fetchRel jsonFieldCode 0xA = some (.auipc ra 0x0, 4) := by decide
theorem fd_at_e : fetchRel jsonFieldCode 0xE = some (.jalr ra ra 0x162, 4) := by decide
theorem fd_at_12 : fetchRel jsonFieldCode 0x12 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem fd_at_16 : fetchRel jsonFieldCode 0x16 = some (.branch .beq a0 x0 0xA, 2) := by decide
theorem fd_at_18 : fetchRel jsonFieldCode 0x18 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem fd_at_1a : fetchRel jsonFieldCode 0x1A = some (.load .lbu a1 sp 0xD, 4) := by decide
theorem fd_at_1e : fetchRel jsonFieldCode 0x1E = some (.jal x0 0x10, 2) := by decide
theorem fd_at_20 : fetchRel jsonFieldCode 0x20 = some (.load .lw a0 sp 0x10, 2) := by decide
theorem fd_at_22 : fetchRel jsonFieldCode 0x22 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem fd_at_24 : fetchRel jsonFieldCode 0x24 = some (.load .lw a1 sp 0x14, 2) := by decide
theorem fd_at_26 : fetchRel jsonFieldCode 0x26 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem fd_at_28 : fetchRel jsonFieldCode 0x28 = some (.jal x0 0xA, 2) := by decide
theorem fd_at_2a : fetchRel jsonFieldCode 0x2A = some (.aluImm .add a1 x0 0x21, 4) := by decide
theorem fd_at_2e : fetchRel jsonFieldCode 0x2E = some (.store .sb (8 : Fin 32) a1 0x4, 4) := by decide
theorem fd_at_32 : fetchRel jsonFieldCode 0x32 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem fd_at_34 : fetchRel jsonFieldCode 0x34 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem fd_at_36 : fetchRel jsonFieldCode 0x36 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem fd_at_38 : fetchRel jsonFieldCode 0x38 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem fd_at_3a : fetchRel jsonFieldCode 0x3A = some (.jalr x0 ra 0x0, 2) := by decide

/-- The result of `field` at `out`. -/
def FieldRes (M M' : Word → BitVec 8) (out : Word) : Except Nat (Word × Nat) → Prop
  | .error e => (∀ x, Sep x 1 out 8 → M' x = M x) ∧ memLoad32 M' out = 0 ∧ M' (out + 4) = BitVec.ofNat 8 e
  | .ok (q, l) => (∀ x, Sep x 1 out 8 → M' x = M x) ∧ memLoad32 M' out = q ∧
      memLoad32 M' (out + 4) = BitVec.ofNat 32 l

/-- `FieldRes` after a function that may also change the `k` bytes at `s`. -/
def FieldResF (M M' : Word → BitVec 8) (out s : Word) (k : Nat) (r : Except Nat (Word × Nat)) : Prop :=
  ∃ M1, Out M M1 s k ∧ FieldRes M1 M' out r

/-- The word-level result of `field` on the value at `p`. -/
def fieldRes (p : Word) (r : Except Nat (Nat × Nat)) : Except Nat (Word × Nat) :=
  r.map fun x => (p + BitVec.ofNat 32 x.1, x.2)

/-- `field` at `b` and `get`, with its callees, at `b + 0x16C`. -/
structure FieldCode (M : Word → BitVec 8) (b : Word) : Prop where
  field : CodeIn M b jsonFieldCode
  get : GetCode M (b + 0x16C)

/-- The `k` bytes at `s` are apart from `field`'s code and every callee's. -/
structure FieldSep (s : Word) (k : Nat) (b : Word) : Prop where
  field : Sep s k b jsonFieldCode.length
  get : GetSep s k (b + 0x16C)

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `get(key)` on the `n` bytes at `p` with the code at `tb`. -/
theorem WP.callGet {hi lo tb p kq out s : Word} {n kl : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : GetCode M tb) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = kq)
    (ha4 : f a4 = BitVec.ofNat 32 kl) (hsp : f sp = s + BitVec.ofNat 32 228)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hsw : s.toNat + 228 < 2 ^ 32) (hkl : kl < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32) (hgs : GetSep s 228 tb) (hSp : Sep s 228 p n)
    (hSk : Sep s 228 kq kl) (hso : Sep out 12 s 228) (hsc : Sep out 12 tb jsonGetCode.length)
    (hSb : Sep s 228 base code.length) (hsb : Sep out 12 base code.length)
    (k : ∀ m2 : Machine, GetResF M m2.mem out s 228 (getRes p (objGet (memBytes M p n) (memBytes M kq kl))) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => GetResF M m2.mem out s 228 (getRes p (objGet (memBytes M p n) (memBytes M kq kl))))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hU⟩ := hP
      exact hU.out.codeIn (hO.codeIn hc hSb) hsb) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonGet_correct m1 (base := tb) (out := out) (s := s) (p := p) (kq := kq)
    (n := n) (kl := kl) htb (by rw [hmem1]; exact hct) hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact ha3)
    (by rw [hreg1]; rsimp; exact ha4) (by rw [hreg1]; rsimp; exact hsp)
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    hal halo hsw hkl hp0 hpn hgs hSp hSk hso hsc
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

end

section
variable {base F : Word} {f g0 : Fin 32 → Word}

theorem fd_epi {R : (Word → BitVec 8) → Prop} {Mf : Word → BitVec 8} (hsp : f sp = F)
    (e1 : memLoad32 Mf (F + 0x1C) = g0 ra) (e2 : memLoad32 Mf (F + 0x18) = g0 8)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x20) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ jClob ++ [ra, sp, 8] → f x = g0 x) (hR : R Mf) :
    WP jsonFieldCode base (RPost (g0 ra) R g0) Mf 0x34 f := by
  refine WP.lw fd_at_34 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x1C) (by decide)) ?_; wn
  refine WP.lw fd_at_36 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x18) (by decide)) ?_; wn
  refine WP.aluImm fd_at_38 ?_; wn
  refine WP.ret fd_at_3a ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]

end

theorem field_err (M : Word → BitVec 8) (out : Word) (b : BitVec 8) (e : Nat) (hv : b = BitVec.ofNat 8 e) :
    FieldRes M (memStore32 (memStore8 M (out + 4) b) out 0) out (.error e) := by
  have h4 : Sep (out + BitVec.ofNat 32 4) 1 out 4 := by
    have := sep_offsets out (c := 4) (n := 1) (d := 0) (k := 4) (Or.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨fun x hx => ?_, memLoad32_store32_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 4 := by
      have := hx.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store32 _ out 0) x h0]
    exact (out_store8 _ (out + 4) _) x (hx.subR (c := 4) (l := 1) (by decide))
  · rw [← hv]; exact ((out_store32 _ out 0) _ h4).trans (memStore8_same _ _ _)

theorem field_ok (M : Word → BitVec 8) (out q : Word) (l : Nat) :
    FieldRes M (memStore32 (memStore32 M (out + 4) (BitVec.ofNat 32 l)) out q) out (.ok (q, l)) := by
  have h4 : Sep (out + BitVec.ofNat 32 0) 4 (out + BitVec.ofNat 32 4) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  rw [add_ofNat_zero] at h4
  refine ⟨fun x hx => ?_, memLoad32_store32_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 4 := by
      have := hx.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store32 _ out q) x h0]
    exact (out_store32 _ (out + 4) _) x (hx.subR (c := 4) (l := 4) (by decide))
  · exact (memLoad32_store32_sep h4).trans (memLoad32_store32_same _ _ _)

theorem FieldRes.out {M M' : Word → BitVec 8} {out : Word} {r : Except Nat (Word × Nat)}
    (h : FieldRes M M' out r) : Out M M' out 8 := by
  rcases r with _ | ⟨_, _⟩
  · exact h.1
  · exact h.1

section
variable {M0 : Word → BitVec 8} {base out s p kq : Word} {n kl : Nat} {f : Fin 32 → Word}

theorem fd_wp (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n) (h3 : f a3 = kq)
    (h4 : f a4 = BitVec.ofNat 32 kl) (hsp : f sp = s + BitVec.ofNat 32 260) (hret : f ra &&& ~~~1 = f ra)
    (hb : base.toNat % 2 = 0) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hsw : s.toNat + 260 < 2 ^ 32)
    (hkl : kl < 2 ^ 32) (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32)
    (hcode : FieldCode M0 base) (hfs : FieldSep s 260 base) (hSp : Sep s 260 p n) (hSk : Sep s 260 kq kl)
    (hso : Sep out 8 s 260) (hsc : Sep out 8 base jsonFieldCode.length) :
    WP jsonFieldCode base (RPost (f ra) (fun M' => FieldResF M0 M' out s 260
      (fieldRes p (objField (memBytes M0 p n) (memBytes M0 kq kl)))) f) M0 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFE0 = s + 228 := by rw [hsp, ev_add, BitVec.add_assoc]; rfl
  refine WP.aluImm fd_at_0 ?_; wn
  rw [esp]
  generalize hF : s + 228 = F
  have hF' : s + BitVec.ofNat 32 228 = F := hF
  have halF : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hal (k := 228) (by decide)
  have hsp0 : f sp = F + BitVec.ofNat 32 0x20 := by rw [hsp, ← hF, BitVec.add_assoc]; rfl
  have hFs : ∀ {c w : Nat}, 228 + c + w ≤ 260 → ∀ {a : Word} {l : Nat}, Sep s 260 a l →
      Sep (F + BitVec.ofNat 32 c) w a l := fun hc _ _ h => by rw [← hF', add_ofNat_assoc]; exact h.sub hc
  have hoS : ∀ {c : Nat}, 228 + c + 4 ≤ 260 → Sep out 8 (F + BitVec.ofNat 32 c) 4 := fun hc => by
    rw [← hF', add_ofNat_assoc]; exact hso.subR hc
  refine WP.sw fd_at_2 (by rsimp; exact aligned_add halF (k := 0x1C) (by decide))
    (by rsimp; exact hFs (by decide) hfs.field) ?_; wn
  refine WP.sw fd_at_4 (by rsimp; exact aligned_add halF (k := 0x18) (by decide))
    (by rsimp; exact hFs (by decide) hfs.field) ?_; wn
  change WP jsonFieldCode base _ (memStore32 (memStore32 M0 (F + 0x1C) (f ra)) (F + 0x18) (f 8)) 0x6 _
  have v1 : memLoad32 (memStore32 (memStore32 M0 (F + 0x1C) (f ra)) (F + 0x18) (f 8)) (F + 0x1C) = f ra :=
    (memLoad32_store32_sep (sep_offsets F (c := 0x18) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by decide))
      (by decide) (by decide))).trans (memLoad32_store32_same _ _ _)
  have v2 : memLoad32 (memStore32 (memStore32 M0 (F + 0x1C) (f ra)) (F + 0x18) (f 8)) (F + 0x18) = f 8 :=
    memLoad32_store32_same _ _ _
  have hO1 : Out M0 (memStore32 (memStore32 M0 (F + 0x1C) (f ra)) (F + 0x18) (f 8)) s 260 :=
    (Out.upK (c := 256) (by rw [← hF', BitVec.add_assoc]; rfl) (out_store32 _ _ _) (by decide)).trans
      (Out.upK (c := 252) (by rw [← hF', BitVec.add_assoc]; rfl) (out_store32 _ _ _) (by decide))
  generalize memStore32 (memStore32 M0 (F + 0x1C) (f ra)) (F + 0x18) (f 8) = M1 at v1 v2 hO1
  have hc1 : FieldCode M1 base := ⟨hO1.codeIn hcode.field hfs.field, hcode.get.out hO1 hfs.get⟩
  have hd1 : memBytes M1 p n = memBytes M0 p n := hO1.bytes hSp
  have hk1 : memBytes M1 kq kl = memBytes M0 kq kl := hO1.bytes hSk
  have hFc : s + BitVec.ofNat 32 240 = F + 0xC := by rw [← hF', BitVec.add_assoc]; rfl
  refine WP.alu fd_at_6 ?_; wn
  refine WP.aluImm fd_at_8 ?_; wn
  refine WP.callGet (tb := base + 0x16C) (out := F + 0xC) (s := s) (p := p) (kq := kq) (n := n) (kl := kl)
    fd_at_a fd_at_e (by simp only [BitVec.add_assoc]; rfl) (even_at base hb _ (by decide)) (by decide) hc1.get
    (by (try rsimp); (try rw [ev_add])) (by (try rsimp); exact h1) (by (try rsimp); exact h2)
    (by (try rsimp); exact h3) (by (try rsimp); exact h4) (by (try rsimp); exact hF'.symm)
    hal (aligned_add halF (k := 12) (by decide)) (by omega) hkl hp0 hpn (hfs.get.low (by decide))
    (sep_low hSp (by decide)) (sep_low hSk (by decide))
    (by rw [← hFc]; have := sep_offsets s (c := 240) (n := 12) (d := 0) (k := 228) (Or.inr (by decide))
          (by decide) (by decide)
        rwa [add_ofNat_zero] at this)
    (hFs (c := 12) (w := 12) (by decide) hfs.get.get) (sep_low hfs.field (by decide))
    (hFs (c := 12) (w := 12) (by decide) hfs.field) fun m2 hR => ?_
  rw [hd1, hk1] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hGR⟩ := hR
  have hO2 : Out M0 M2 s 260 := hO1.trans ((hOa.mono (by decide)).trans (Out.upK hFc hGR.out (by decide)))
  have e1 : memLoad32 M2 (F + 0x1C) = f ra := by
    refine ((hGR.out.load32 ?_).trans (hOa.load32 ?_)).trans v1
    · exact sep_offsets F (c := 12) (n := 12) (d := 0x1C) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
    · show Sep s 228 (F + BitVec.ofNat 32 0x1C) 4
      rw [← hF', add_ofNat_assoc]
      have := sep_offsets s (c := 0) (n := 228) (d := 256) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
  have e2 : memLoad32 M2 (F + 0x18) = f 8 := by
    refine ((hGR.out.load32 ?_).trans (hOa.load32 ?_)).trans v2
    · exact sep_offsets F (c := 12) (n := 12) (d := 0x18) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
    · show Sep s 228 (F + BitVec.ofNat 32 0x18) 4
      rw [← hF', add_ofNat_assoc]
      have := sep_offsets s (c := 0) (n := 228) (d := 252) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
  refine WP.zero fun hz2 => ?_
  refine WP.lbu fd_at_12 ?_; wn
  unfold objField
  rcases hog : objGet (memBytes M0 p n) (memBytes M0 kq kl) with e | (_ | ⟨vp, vl⟩) <;> rw [hog] at hGR
  · obtain ⟨-, t1, t2⟩ := hGR
    refine WP.branch fd_at_16 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [t1] at eb; exact absurd eb (by decide)
    refine WP.aluImm fd_at_18 ?_; wn
    refine WP.lbu fd_at_1a ?_; wn
    refine WP.jal fd_at_1e (by decide) ?_; wn
    have t2' : M2 (F + 0xD) = BitVec.ofNat 8 e := by
      rw [show F + 0xD = F + 12 + 1 by rw [BitVec.add_assoc]; rfl]; exact t2
    have hs4 : Sep (out + BitVec.ofNat 32 4) 1 base jsonFieldCode.length := hsc.sub (by decide)
    refine WP.sb fd_at_2e (by (try rsimp); (try simp only [ev0]); rw [h0]; exact hs4) ?_; wn
    refine WP.sw fd_at_32 (by (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero]; exact halo)
      (by (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero]; exact sep_low hsc (by decide)) ?_
    wn
    (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero, t2', ri_ze]
    have hOf : Out M2 (memStore32 (memStore8 M2 (out + 4) (BitVec.ofNat 8 e)) out 0) out 8 :=
      (Out.widen (d := 4) (out_store8 _ _ _) (by decide)).trans ((out_store32 _ _ _).mono (by decide))
    refine fd_epi (by rsimp) ((hOf.load32 (hoS (by decide))).trans e1) ((hOf.load32 (hoS (by decide))).trans e2)
      hsp0 hret halF hz (by keepz hz) ⟨M2, hO2, field_err M2 out _ e rfl⟩
  · obtain ⟨-, t1, t2⟩ := hGR
    have t2' : memLoad32 M2 (F + 0x10) = 0 := by
      rw [show F + 0x10 = F + 0xC + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch fd_at_16 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [t1] at eb; exact absurd eb (by decide)
    refine WP.lw fd_at_20 (by (try rsimp); exact aligned_add halF (k := 0x10) (by decide)) ?_; wn
    refine WP.branch fd_at_22 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [t2'] at eb; exact absurd eb (by decide)
    refine WP.aluImm fd_at_2a ?_; wn
    have hs4 : Sep (out + BitVec.ofNat 32 4) 1 base jsonFieldCode.length := hsc.sub (by decide)
    refine WP.sb fd_at_2e (by (try rsimp); (try simp only [ev0]); rw [h0]; exact hs4) ?_; wn
    refine WP.sw fd_at_32 (by (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero]; exact halo)
      (by (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero]; exact sep_low hsc (by decide)) ?_
    wn
    (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero, t2']
    have hOf : Out M2 (memStore32 (memStore8 M2 (out + 4) (BitVec.extractLsb' 0 8 (33 : Word))) out 0) out 8 :=
      (Out.widen (d := 4) (out_store8 _ _ _) (by decide)).trans ((out_store32 _ _ _).mono (by decide))
    refine fd_epi (by rsimp) ((hOf.load32 (hoS (by decide))).trans e1) ((hOf.load32 (hoS (by decide))).trans e2)
      hsp0 hret halF hz (by keepz hz) ⟨M2, hO2, field_err M2 out _ 33 (by decide)⟩
  · obtain ⟨-, t1, t2, t3⟩ := hGR
    have t2' : memLoad32 M2 (F + 0x10) = p + BitVec.ofNat 32 vp := by
      rw [show F + 0x10 = F + 0xC + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    have t3' : memLoad32 M2 (F + 0x14) = BitVec.ofNat 32 vl := by
      rw [show F + 0x14 = F + 0xC + 8 by rw [BitVec.add_assoc]; rfl]; exact t3
    have hv := objGet_val hog
    rw [memBytes_length] at hv
    have hq0 := nx_q0 hp0 (n := n) (pos := vp) (by omega) hv.1
    refine WP.branch fd_at_16 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [t1] at eb; exact absurd eb (by decide)
    refine WP.lw fd_at_20 (by (try rsimp); exact aligned_add halF (k := 0x10) (by decide)) ?_; wn
    refine WP.branch fd_at_22 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [t2', hq0] at eb; exact absurd eb (by decide)
    refine WP.lw fd_at_24 (by (try rsimp); exact aligned_add halF (k := 0x14) (by decide)) ?_; wn
    have hs4 : Sep (out + BitVec.ofNat 32 4) 4 base jsonFieldCode.length := hsc.sub (by decide)
    refine WP.sw fd_at_26 (by (try rsimp); (try simp only [ev0]); rw [h0]; exact aligned_add halo (k := 4) (by decide))
      (by (try rsimp); (try simp only [ev0]); rw [h0]; exact hs4) ?_; wn
    refine WP.jal fd_at_28 (by decide) ?_; wn
    refine WP.sw fd_at_32 (by (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero]; exact halo)
      (by (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero]; exact sep_low hsc (by decide)) ?_
    wn
    (try rsimp); (try simp only [ev0]); rw [h0, add_lit_zero, t2', t3']
    have hOf : Out M2 (memStore32 (memStore32 M2 (out + 4) (BitVec.ofNat 32 vl)) out (p + BitVec.ofNat 32 vp))
        out 8 :=
      (Out.widen (d := 4) (out_store32 _ _ _) (by decide)).trans ((out_store32 _ _ _).mono (by decide))
    refine fd_epi (by rsimp) ((hOf.load32 (hoS (by decide))).trans e1) ((hOf.load32 (hoS (by decide))).trans e2)
      hsp0 hret halF hz (by keepz hz) ⟨M2, hO2, field_ok M2 out _ vl⟩

end

/-- `field(key)` on the `n` bytes at `p`, with the key the `kl` bytes at `kq`
and `sp = s + 260`, returns with `out` holding `objField doc key`, its offset
moved to an address by `fieldRes p`: the value of the first member whose key
equals the key, or the error byte (`0x21` when the document isn't an object
or has no such member, `0x20` when a member isn't valid JSON). It changes
memory only in the 260 bytes at `s` and the 8 bytes at `out`, and keeps
every register outside `jClob`. The callees are where `FieldCode` lists
them. -/
theorem jsonField_correct (m : Machine) {base retAddr out s p kq : Word} {n kl : Nat}
    (hb : base.toNat % 2 = 0) (hc : FieldCode m.mem base) (hpc : m.pc = base) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n) (ha3 : reg m a3 = kq)
    (ha4 : reg m a4 = BitVec.ofNat 32 kl) (hsp : reg m sp = s + BitVec.ofNat 32 260) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hsw : s.toNat + 260 < 2 ^ 32) (hkl : kl < 2 ^ 32) (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32)
    (hfs : FieldSep s 260 base) (hSp : Sep s 260 p n) (hSk : Sep s 260 kq kl) (hso : Sep out 8 s 260)
    (hsc : Sep out 8 base jsonFieldCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      FieldResF m.mem m'.mem out s 260 (fieldRes p (objField (memBytes m.mem p n) (memBytes m.mem kq kl))) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (fd_wp ha0 ha1 ha2 ha3 ha4 hsp (by rw [hra]; exact hret) hb hal halo
    hsw hkl hp0 hpn hc hfs hSp hSk hso hsc) hb hc.field hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
