import C3BootProofs.Proofs.JsonNextElement
import C3BootProofs.Proofs.JsonKeyEnd

/-!
# `Members::next_member`, as compiled

`next_member` on the cursor at `c`, whose words are the object's pointer
`p`, its length `n`, and the position `pos`, returns `Ok(None)` when the byte
at `pos` is `}`. Otherwise it finds the key with `string_end` in canonical
mode, the value's start with `key_end` in strict mode, and the value with
`read_item`, and returns `Ok(Some((key, value)))`, moving the cursor's
position to the item's `after`.

The result has the layout `MemRes` describes: a zero byte at `out`, the key's
pointer at `out + 4` (zero for `None`) and its length at `out + 8`, and the
value's pointer and length at `out + 12` and `out + 16`; or the byte `1` at
`out` and the error byte `0x20` at `out + 1`. The function saves eight
registers in a 48-byte frame, and `read_item` uses 116 more bytes, so the
stack region is the 164 bytes below `sp`. `jsonNextMember_correct` is the
contract.
-/

namespace C3.Json

/-- The value of the member whose key starts at `pos` and has length `l`. -/
def memberKey (d : Bytes) (pos l : Nat) : Option (Option (Nat × Nat × Nat × Nat × Nat)) :=
  match keyEnd false d pos with
  | none => none
  | some v => (readItem d v).map fun x => some (pos + 1, l, v, x.1 - v, x.2)

/-- The rest of `next_member` once the key's closing quote is at `e - 1`. -/
def memberTail (d : Bytes) (pos e : Nat) : Option (Option (Nat × Nat × Nat × Nat × Nat)) :=
  if e = 0 ∨ e - 1 ≤ pos ∨ d.length < e - 1 then none else memberKey d pos (e - 1 - (pos + 1))

/-- `next_member` at `pos`: `some none` at the closing brace, otherwise the
key's start and length, the value's start and length, and `after`. -/
def nextMember (d : Bytes) (pos : Nat) : Option (Option (Nat × Nat × Nat × Nat × Nat)) :=
  if pos < d.length ∧ d.getD pos 0 = 125 then some none
  else (stringEnd true d pos).bind (memberTail d pos)

theorem keyEnd_le {c : Bool} {d : Bytes} {pos v : Nat} (h : keyEnd c d pos = some v) : v ≤ d.length := by
  unfold keyEnd at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i e _
  split at h
  · cases h
  split at h
  · cases h
  cases h
  have := wsIn_le c d (wsIn c d e + 1)
  omega

theorem stringEnd_none {c : Bool} {d : Bytes} {pos : Nat} (h : d.length ≤ pos) : stringEnd c d pos = none :=
  ite_eq_left_of_eq_true _ _ (eq_true h)

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem nm_at_0 : fetchRel jsonNextMemberCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem nm_at_2 : fetchRel jsonNextMemberCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem nm_at_4 : fetchRel jsonNextMemberCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem nm_at_6 : fetchRel jsonNextMemberCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem nm_at_8 : fetchRel jsonNextMemberCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem nm_at_a : fetchRel jsonNextMemberCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem nm_at_c : fetchRel jsonNextMemberCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem nm_at_e : fetchRel jsonNextMemberCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem nm_at_10 : fetchRel jsonNextMemberCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x10, 2) := by decide
theorem nm_at_12 : fetchRel jsonNextMemberCode 0x12 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem nm_at_14 : fetchRel jsonNextMemberCode 0x14 = some (.load .lw (20 : Fin 32) a1 0x4, 4) := by decide
theorem nm_at_18 : fetchRel jsonNextMemberCode 0x18 = some (.load .lw (8 : Fin 32) a1 0x8, 2) := by decide
theorem nm_at_1a : fetchRel jsonNextMemberCode 0x1A = some (.load .lw (19 : Fin 32) a1 0x0, 4) := by decide
theorem nm_at_1e : fetchRel jsonNextMemberCode 0x1E = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem nm_at_20 : fetchRel jsonNextMemberCode 0x20 = some (.branch .bgeu (8 : Fin 32) (20 : Fin 32) 0x1A, 4) := by decide
theorem nm_at_24 : fetchRel jsonNextMemberCode 0x24 = some (.alu .add a0 (19 : Fin 32) (8 : Fin 32), 4) := by decide
theorem nm_at_28 : fetchRel jsonNextMemberCode 0x28 = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem nm_at_2c : fetchRel jsonNextMemberCode 0x2C = some (.aluImm .add a0 a0 0xFFFFFF83, 4) := by decide
theorem nm_at_30 : fetchRel jsonNextMemberCode 0x30 = some (.branch .bne a0 x0 0x10, 2) := by decide
theorem nm_at_32 : fetchRel jsonNextMemberCode 0x32 = some (.aluImm .add (21 : Fin 32) x0 0x0, 2) := by decide
theorem nm_at_34 : fetchRel jsonNextMemberCode 0x34 = some (.store .sw (18 : Fin 32) x0 0x4, 4) := by decide
theorem nm_at_38 : fetchRel jsonNextMemberCode 0x38 = some (.jal x0 0x64, 2) := by decide
theorem nm_at_3a : fetchRel jsonNextMemberCode 0x3A = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem nm_at_3c : fetchRel jsonNextMemberCode 0x3C = some (.branch .beq (8 : Fin 32) a0 0x56, 4) := by decide
theorem nm_at_40 : fetchRel jsonNextMemberCode 0x40 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem nm_at_42 : fetchRel jsonNextMemberCode 0x42 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem nm_at_44 : fetchRel jsonNextMemberCode 0x44 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem nm_at_46 : fetchRel jsonNextMemberCode 0x46 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem nm_at_48 : fetchRel jsonNextMemberCode 0x48 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem nm_at_4a : fetchRel jsonNextMemberCode 0x4A = some (.aluImm .add (21 : Fin 32) x0 0x1, 2) := by decide
theorem nm_at_4c : fetchRel jsonNextMemberCode 0x4C = some (.auipc ra 0x0, 4) := by decide
theorem nm_at_50 : fetchRel jsonNextMemberCode 0x50 = some (.jalr ra ra 0x9E, 4) := by decide
theorem nm_at_54 : fetchRel jsonNextMemberCode 0x54 = some (.load .lbu a0 sp 0x4, 4) := by decide
theorem nm_at_58 : fetchRel jsonNextMemberCode 0x58 = some (.branch .beq a0 x0 0xC, 2) := by decide
theorem nm_at_5a : fetchRel jsonNextMemberCode 0x5A = some (.load .lbu a0 sp 0x5, 4) := by decide
theorem nm_at_5e : fetchRel jsonNextMemberCode 0x5E = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem nm_at_62 : fetchRel jsonNextMemberCode 0x62 = some (.jal x0 0x3A, 2) := by decide
theorem nm_at_64 : fetchRel jsonNextMemberCode 0x64 = some (.load .lw (22 : Fin 32) sp 0x8, 2) := by decide
theorem nm_at_66 : fetchRel jsonNextMemberCode 0x66 = some (.branch .beq (22 : Fin 32) x0 0x2C, 4) := by decide
theorem nm_at_6a : fetchRel jsonNextMemberCode 0x6A = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem nm_at_6c : fetchRel jsonNextMemberCode 0x6C = some (.branch .bgeu (8 : Fin 32) (22 : Fin 32) 0x26, 4) := by decide
theorem nm_at_70 : fetchRel jsonNextMemberCode 0x70 = some (.branch .bltu (20 : Fin 32) (22 : Fin 32) 0x22, 4) := by decide
theorem nm_at_74 : fetchRel jsonNextMemberCode 0x74 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem nm_at_76 : fetchRel jsonNextMemberCode 0x76 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem nm_at_78 : fetchRel jsonNextMemberCode 0x78 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem nm_at_7a : fetchRel jsonNextMemberCode 0x7A = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem nm_at_7c : fetchRel jsonNextMemberCode 0x7C = some (.aluImm .add a4 x0 0x0, 2) := by decide
theorem nm_at_7e : fetchRel jsonNextMemberCode 0x7E = some (.auipc ra 0x0, 4) := by decide
theorem nm_at_82 : fetchRel jsonNextMemberCode 0x82 = some (.jalr ra ra 0xC6, 4) := by decide
theorem nm_at_86 : fetchRel jsonNextMemberCode 0x86 = some (.load .lbu a0 sp 0x4, 4) := by decide
theorem nm_at_8a : fetchRel jsonNextMemberCode 0x8A = some (.branch .beq a0 x0 0x2A, 2) := by decide
theorem nm_at_8c : fetchRel jsonNextMemberCode 0x8C = some (.load .lbu a0 sp 0x5, 4) := by decide
theorem nm_at_90 : fetchRel jsonNextMemberCode 0x90 = some (.jal x0 0x6, 2) := by decide
theorem nm_at_92 : fetchRel jsonNextMemberCode 0x92 = some (.aluImm .add a0 x0 0x20, 4) := by decide
theorem nm_at_96 : fetchRel jsonNextMemberCode 0x96 = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem nm_at_9a : fetchRel jsonNextMemberCode 0x9A = some (.aluImm .add (21 : Fin 32) x0 0x1, 2) := by decide
theorem nm_at_9c : fetchRel jsonNextMemberCode 0x9C = some (.store .sb (18 : Fin 32) (21 : Fin 32) 0x0, 4) := by decide
theorem nm_at_a0 : fetchRel jsonNextMemberCode 0xA0 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem nm_at_a2 : fetchRel jsonNextMemberCode 0xA2 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem nm_at_a4 : fetchRel jsonNextMemberCode 0xA4 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem nm_at_a6 : fetchRel jsonNextMemberCode 0xA6 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem nm_at_a8 : fetchRel jsonNextMemberCode 0xA8 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem nm_at_aa : fetchRel jsonNextMemberCode 0xAA = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem nm_at_ac : fetchRel jsonNextMemberCode 0xAC = some (.load .lw (21 : Fin 32) sp 0x14, 2) := by decide
theorem nm_at_ae : fetchRel jsonNextMemberCode 0xAE = some (.load .lw (22 : Fin 32) sp 0x10, 2) := by decide
theorem nm_at_b0 : fetchRel jsonNextMemberCode 0xB0 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem nm_at_b2 : fetchRel jsonNextMemberCode 0xB2 = some (.jalr x0 ra 0x0, 2) := by decide
theorem nm_at_b4 : fetchRel jsonNextMemberCode 0xB4 = some (.load .lw a3 sp 0x8, 2) := by decide
theorem nm_at_b6 : fetchRel jsonNextMemberCode 0xB6 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem nm_at_b8 : fetchRel jsonNextMemberCode 0xB8 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem nm_at_ba : fetchRel jsonNextMemberCode 0xBA = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem nm_at_bc : fetchRel jsonNextMemberCode 0xBC = some (.auipc ra 0x0, 4) := by decide
theorem nm_at_c0 : fetchRel jsonNextMemberCode 0xC0 = some (.jalr ra ra 0x122, 4) := by decide
theorem nm_at_c4 : fetchRel jsonNextMemberCode 0xC4 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem nm_at_c6 : fetchRel jsonNextMemberCode 0xC6 = some (.branch .beq a0 x0 0x1E, 2) := by decide
theorem nm_at_c8 : fetchRel jsonNextMemberCode 0xC8 = some (.aluImm .add (21 : Fin 32) x0 0x0, 2) := by decide
theorem nm_at_ca : fetchRel jsonNextMemberCode 0xCA = some (.load .lw a1 sp 0xC, 2) := by decide
theorem nm_at_cc : fetchRel jsonNextMemberCode 0xCC = some (.load .lw a2 sp 0x8, 2) := by decide
theorem nm_at_ce : fetchRel jsonNextMemberCode 0xCE = some (.store .sw (9 : Fin 32) a1 0x8, 2) := by decide
theorem nm_at_d0 : fetchRel jsonNextMemberCode 0xD0 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem nm_at_d2 : fetchRel jsonNextMemberCode 0xD2 = some (.alu .sub a1 (22 : Fin 32) (8 : Fin 32), 4) := by decide
theorem nm_at_d6 : fetchRel jsonNextMemberCode 0xD6 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (19 : Fin 32), 2) := by decide
theorem nm_at_d8 : fetchRel jsonNextMemberCode 0xD8 = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem nm_at_da : fetchRel jsonNextMemberCode 0xDA = some (.store .sw a3 (8 : Fin 32) 0x4, 2) := by decide
theorem nm_at_dc : fetchRel jsonNextMemberCode 0xDC = some (.store .sw a3 a1 0x8, 2) := by decide
theorem nm_at_de : fetchRel jsonNextMemberCode 0xDE = some (.store .sw a3 a0 0xC, 2) := by decide
theorem nm_at_e0 : fetchRel jsonNextMemberCode 0xE0 = some (.store .sw a3 a2 0x10, 2) := by decide
theorem nm_at_e2 : fetchRel jsonNextMemberCode 0xE2 = some (.jal x0 0xFFFFFFBA, 2) := by decide
theorem nm_at_e4 : fetchRel jsonNextMemberCode 0xE4 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem nm_at_e8 : fetchRel jsonNextMemberCode 0xE8 = some (.jal x0 0xFFFFFFAE, 2) := by decide

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
  {f : Fin 32 → Word}

/-- A call to `key_end(doc, pos, mode)` with the code at `tb`, its frame in
the 32 bytes at `s`, storing its result at `out`. -/
theorem WP.callKeyEnd {hi lo tb p out s : Word} {n pos : Nat} {cm : Bool}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonKeyEndCode) (hcs : CodeIn M (tb + 0xFFFFFFA6) jsonStringEndCode)
    (hcw : CodeIn M (tb + 0x322) jsonSkipWsCode)
    (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = BitVec.ofNat 32 pos)
    (ha4 : f a4 = modeW cm) (hsp : f sp = s + BitVec.ofNat 32 32) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hSc : Sep s 32 tb jsonKeyEndCode.length)
    (hSs : Sep s 32 (tb + 0xFFFFFFA6) jsonStringEndCode.length)
    (hSw : Sep s 32 (tb + 0x322) jsonSkipWsCode.length) (hSp : Sep s 32 p n) (hso : Sep out 8 s 32)
    (hsc : Sep out 8 tb jsonKeyEndCode.length) (hSb : Sep s 32 base code.length)
    (hsb : Sep out 8 base code.length)
    (k : ∀ m2 : Machine, UsizeResF M m2.mem out s 32 (keyEnd cm (memBytes M p n) pos) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => UsizeResF M m2.mem out s 32 (keyEnd cm (memBytes M p n) pos))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hU⟩ := hP
      exact hU.out.codeIn (hO.codeIn hc hSb) hsb) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonKeyEnd_correct m1 (base := tb) (out := out) (s := s) (p := p) (n := n)
    (pos := pos) (c := cm) htb (by rw [hmem1]; exact hct) (by rw [hmem1]; exact hcs) (by rw [hmem1]; exact hcw)
    hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact ha3) (by rw [hreg1]; rsimp; exact ha4)
    (by rw [hreg1]; rsimp; exact hsp) hn hpos hal halo (retAddr := base + BitVec.ofNat 32 (off + 8))
    (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev)) hSc hSs hSw hSp hso hsc
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

end

/-- `out` holds `r` as a `Result<Option<(&[u8], Value)>, TufError>`, and the
cursor at `c` holds the new position after a member. -/
def MemRes (M M' : Word → BitVec 8) (out c : Word) : Option (Option (Word × Nat × Word × Nat × Nat)) → Prop
  | none => (∀ x, Sep x 1 out 20 → M' x = M x) ∧ M' out = 1 ∧ M' (out + 1) = 0x20
  | some none => (∀ x, Sep x 1 out 20 → M' x = M x) ∧ M' out = 0 ∧ memLoad32 M' (out + 4) = 0
  | some (some (kq, kl, vq, vl, a)) => (∀ x, Sep x 1 out 20 → Sep x 1 (c + 8) 4 → M' x = M x) ∧ M' out = 0 ∧
      memLoad32 M' (out + 4) = kq ∧ memLoad32 M' (out + 8) = BitVec.ofNat 32 kl ∧
      memLoad32 M' (out + 12) = vq ∧ memLoad32 M' (out + 16) = BitVec.ofNat 32 vl ∧
      memLoad32 M' (c + 8) = BitVec.ofNat 32 a

/-- `MemRes` after a function that may also change the `k` bytes at `s`. -/
def MemResF (M M' : Word → BitVec 8) (out c s : Word) (k : Nat)
    (r : Option (Option (Word × Nat × Word × Nat × Nat))) : Prop :=
  ∃ M1, Out M M1 s k ∧ MemRes M1 M' out c r

/-- The word-level result of `next_member` on the object at `p`. -/
def memRes (p : Word) (r : Option (Option (Nat × Nat × Nat × Nat × Nat))) :
    Option (Option (Word × Nat × Word × Nat × Nat)) :=
  r.map (Option.map fun x => (p + BitVec.ofNat 32 x.1, x.2.1, p + BitVec.ofNat 32 x.2.2.1, x.2.2.2.1, x.2.2.2.2))

theorem MemRes.out {M M' : Word → BitVec 8} {out c x : Word} {r : Option (Option (Word × Nat × Word × Nat × Nat))}
    (h : MemRes M M' out c r) (ho : Sep x 1 out 20) (hc : Sep x 1 (c + 8) 4) : M' x = M x := by
  rcases r with _ | _ | ⟨_, _, _, _, _⟩
  · exact h.1 x ho
  · exact h.1 x ho
  · exact h.1 x ho hc

theorem MemRes.slots {M M' M1 : Word → BitVec 8} {out c F : Word} {cs : List Nat}
    {r : Option (Option (Word × Nat × Word × Nat × Nat))} (h : MemRes M M' out c r) (hS : Slots cs F M1 M)
    (ho : ∀ d, d ∈ cs → Sep out 20 (F + BitVec.ofNat 32 d) 4)
    (hc : ∀ d, d ∈ cs → Sep (c + 8) 4 (F + BitVec.ofNat 32 d) 4) : Slots cs F M1 M' :=
  fun d hd => (memLoad32_congr fun _ hj => h.out (sep_pt (ho d hd) hj) (sep_pt (hc d hd) hj)).trans (hS d hd)

theorem mem_err (M : Word → BitVec 8) (out c : Word) :
    MemRes M (memStore8 (memStore8 M (out + 1) 0x20) out 1) out c none := by
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 1) x h0]
    exact (out_store8 _ (out + 1) 0x20) x (hx.subR (c := 1) (l := 1) (by decide))
  · rw [memStore8_ne (ne_add_one out), memStore8_same]

theorem mem_end (M : Word → BitVec 8) (out c : Word) :
    MemRes M (memStore8 (memStore32 M (out + 4) 0) out 0) out c (some none) := by
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 0) x h0]
    exact (out_store32 _ (out + 4) 0) x (hx.subR (c := 4) (l := 4) (by decide))
  · exact ((out_store8 _ out 0).load32 (sep_o4 out (d := 4) (by decide) (by decide))).trans
      (memLoad32_store32_same _ _ _)

theorem sep_o20 (out : Word) {d : Nat} (hd : 1 ≤ d) (hd2 : d + 4 ≤ 20) : Sep out 1 (out + BitVec.ofNat 32 d) 4 := by
  have := sep_offsets out (c := 0) (n := 1) (d := d) (k := 4) (Or.inl hd) (by decide) (by omega)
  rwa [add_ofNat_zero] at this

theorem mem_ok (M : Word → BitVec 8) {out c : Word} (kq : Word) (kl : Nat) (vq : Word) (vl a : Nat)
    (hoc : Sep out 20 c 12) :
    MemRes M (memStore8 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (c + 8)
      (BitVec.ofNat 32 a)) (out + 4) kq) (out + 8) (BitVec.ofNat 32 kl)) (out + 12) vq) (out + 16)
      (BitVec.ofNat 32 vl)) out 0) out c (some (some (kq, kl, vq, vl, a))) := by
  have so : ∀ i j, i + 4 ≤ j ∨ j + 4 ≤ i → j + 4 ≤ 20 → i + 4 ≤ 20 →
      Sep (out + BitVec.ofNat 32 j) 4 (out + BitVec.ofNat 32 i) 4 := fun i j h hj hi =>
    sep_offsets out (h.symm) (by omega) (by omega)
  have sc : ∀ j, j + 4 ≤ 20 → Sep (out + BitVec.ofNat 32 j) 4 (c + BitVec.ofNat 32 8) 4 := fun j hj =>
    (hoc.sub (c := j) (l := 4) hj).subR (c := 8) (l := 4) (by decide)
  have hc0 : Sep out 1 (c + BitVec.ofNat 32 8) 4 := by
    have := (hoc.sub (c := 0) (l := 1) (by decide)).subR (c := 8) (l := 4) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨fun x hx hc => ?_, memStore8_same _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 0) x h0, (out_store32 _ (out + 16) _) x (hx.subR (c := 16) (l := 4) (by decide)),
      (out_store32 _ (out + 12) _) x (hx.subR (c := 12) (l := 4) (by decide)),
      (out_store32 _ (out + 8) _) x (hx.subR (c := 8) (l := 4) (by decide)),
      (out_store32 _ (out + 4) _) x (hx.subR (c := 4) (l := 4) (by decide)), (out_store32 _ (c + 8) _) x hc]
  · exact ((out_store8 _ out 0).load32 (sep_o20 out (d := 4) (by decide) (by decide))).trans <|
      (memLoad32_store32_sep (so 4 16 (by decide) (by decide) (by decide))).trans <|
      (memLoad32_store32_sep (so 4 12 (by decide) (by decide) (by decide))).trans <|
      (memLoad32_store32_sep (so 4 8 (by decide) (by decide) (by decide))).trans (memLoad32_store32_same _ _ _)
  · exact ((out_store8 _ out 0).load32 (sep_o20 out (d := 8) (by decide) (by decide))).trans <|
      (memLoad32_store32_sep (so 8 16 (by decide) (by decide) (by decide))).trans <|
      (memLoad32_store32_sep (so 8 12 (by decide) (by decide) (by decide))).trans (memLoad32_store32_same _ _ _)
  · exact ((out_store8 _ out 0).load32 (sep_o20 out (d := 12) (by decide) (by decide))).trans <|
      (memLoad32_store32_sep (so 12 16 (by decide) (by decide) (by decide))).trans (memLoad32_store32_same _ _ _)
  · exact ((out_store8 _ out 0).load32 (sep_o20 out (d := 16) (by decide) (by decide))).trans
      (memLoad32_store32_same _ _ _)
  · exact ((out_store8 _ out 0).load32 hc0).trans <|
      (memLoad32_store32_sep (sc 16 (by decide))).trans <| (memLoad32_store32_sep (sc 12 (by decide))).trans <|
      (memLoad32_store32_sep (sc 8 (by decide))).trans <| (memLoad32_store32_sep (sc 4 (by decide))).trans
      (memLoad32_store32_same _ _ _)

/-- The registers `next_member` changes before its epilogue restores the saved ones. -/
abbrev nmE : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21, 22]

abbrev nmCs : List Nat := [0x10, 0x14, 0x18, 0x1C, 0x20, 0x24, 0x28, 0x2C]

/-- The saved registers in the frame at `F`. -/
def NmSaved (F : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (F + BitVec.ofNat 32 0x2C) = g0 ra ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x28) = g0 8 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x24) = g0 9 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x20) = g0 18 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x1C) = g0 19 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x18) = g0 20 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x14) = g0 21 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x10) = g0 22

/-- Memory after the prologue. -/
def nmM1 (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
    (F + 0x2C) (g0 ra)) (F + 0x28) (g0 8)) (F + 0x24) (g0 9)) (F + 0x20) (g0 18)) (F + 0x1C) (g0 19))
    (F + 0x18) (g0 20)) (F + 0x14) (g0 21)) (F + 0x10) (g0 22)

theorem nm_ld {M : Word → BitVec 8} {F v : Word} (c : Nat) (hc : c ∈ nmCs) (ds : List Nat)
    (hd : ∀ d, d ∈ ds → c + 4 ≤ d ∨ d + 4 ≤ c) (hds : ∀ d, d ∈ ds → d + 4 ≤ 48)
    (h : memLoad32 M (F + BitVec.ofNat 32 c) = v) (ws : List Word) :
    memLoad32 ((ds.zip ws).foldl (fun M' x => memStore32 M' (F + BitVec.ofNat 32 x.1) x.2) M)
      (F + BitVec.ofNat 32 c) = v := by
  induction ds generalizing M ws with
  | nil => exact h
  | cons d ds ih =>
    cases ws with
    | nil => exact h
    | cons w ws =>
      have h1 : c + 4 ≤ 48 := by
        simp only [nmCs, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ih (fun d hd' => hd d (List.mem_cons_of_mem _ hd')) (fun d hd' => hds d (List.mem_cons_of_mem _ hd'))
        (ld_skip c d (hd d (List.mem_cons_self ..)) (by omega) (by have := hds d (List.mem_cons_self ..); omega) h) ws

theorem nm_pro (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) :
    Out M (nmM1 M F g0) F 48 ∧ NmSaved F g0 (nmM1 M F g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((((out_store32 _ _ _).widen (d := 0x2C) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x28) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x24) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x20) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x1C) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x18) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x14) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x10) (by decide)))
  · exact nm_ld 0x2C (by decide) [0x28, 0x24, 0x20, 0x1C, 0x18, 0x14, 0x10] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 8, g0 9, g0 18, g0 19, g0 20, g0 21, g0 22]
  · exact nm_ld 0x28 (by decide) [0x24, 0x20, 0x1C, 0x18, 0x14, 0x10] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 9, g0 18, g0 19, g0 20, g0 21, g0 22]
  · exact nm_ld 0x24 (by decide) [0x20, 0x1C, 0x18, 0x14, 0x10] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 18, g0 19, g0 20, g0 21, g0 22]
  · exact nm_ld 0x20 (by decide) [0x1C, 0x18, 0x14, 0x10] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 19, g0 20, g0 21, g0 22]
  · exact nm_ld 0x1C (by decide) [0x18, 0x14, 0x10] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 20, g0 21, g0 22]
  · exact nm_ld 0x18 (by decide) [0x14, 0x10] (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 21, g0 22]
  · exact nm_ld 0x14 (by decide) [0x10] (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 22]
  · exact memLoad32_store32_same _ _ _

section
variable {M1 Mf : Word → BitVec 8} {base F : Word} {f g0 : Fin 32 → Word}

theorem nm_epi {R : (Word → BitVec 8) → Prop} (hsp : f sp = F)
    (hS : Slots nmCs F M1 Mf) (hv : NmSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ nmE → f x = g0 x) (hR : R Mf) :
    WP jsonNextMemberCode base (RPost (g0 ra) R g0) Mf 0xA0 f := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := hv
  have e1 : memLoad32 Mf (F + 0x2C) = g0 ra := (hS 0x2C (by decide)).trans v1
  have e2 : memLoad32 Mf (F + 0x28) = g0 8 := (hS 0x28 (by decide)).trans v2
  have e3 : memLoad32 Mf (F + 0x24) = g0 9 := (hS 0x24 (by decide)).trans v3
  have e4 : memLoad32 Mf (F + 0x20) = g0 18 := (hS 0x20 (by decide)).trans v4
  have e5 : memLoad32 Mf (F + 0x1C) = g0 19 := (hS 0x1C (by decide)).trans v5
  have e6 : memLoad32 Mf (F + 0x18) = g0 20 := (hS 0x18 (by decide)).trans v6
  have e7 : memLoad32 Mf (F + 0x14) = g0 21 := (hS 0x14 (by decide)).trans v7
  have e8 : memLoad32 Mf (F + 0x10) = g0 22 := (hS 0x10 (by decide)).trans v8
  refine WP.lw nm_at_a0 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x2C) (by decide)) ?_; wn
  refine WP.lw nm_at_a2 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x28) (by decide)) ?_; wn
  refine WP.lw nm_at_a4 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x24) (by decide)) ?_; wn
  refine WP.lw nm_at_a6 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x20) (by decide)) ?_; wn
  refine WP.lw nm_at_a8 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x1C) (by decide)) ?_; wn
  refine WP.lw nm_at_aa (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x18) (by decide)) ?_; wn
  refine WP.lw nm_at_ac (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x14) (by decide)) ?_; wn
  refine WP.lw nm_at_ae (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x10) (by decide)) ?_; wn
  refine WP.aluImm nm_at_b0 ?_; wn
  refine WP.ret nm_at_b2 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18, 19, 20, 21, 22]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]
  · rw [hsp, e5]
  · rw [hsp, e6]
  · rw [hsp, e7]
  · rw [hsp, e8]

theorem nm_9c {R : (Word → BitVec 8) → Prop} {out : Word} (hsp : f sp = F) (h18 : f 18 = out)
    (hS : Slots nmCs F M1 Mf) (hv : NmSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ nmE → f x = g0 x) (hsoF : Sep out 1 F 48) (hso1 : Sep out 1 base jsonNextMemberCode.length)
    (hR : R (memStore8 Mf out ((f 21).extractLsb' 0 8))) :
    WP jsonNextMemberCode base (RPost (g0 ra) R g0) Mf 0x9C f := by
  refine WP.sb nm_at_9c (by (try rsimp); rw [h18, add_lit_zero]; exact hso1) ?_; wn
  rw [h18, add_lit_zero]
  exact nm_epi hsp (hS.out (out_store8 _ _ _) (slots_sep_out hsoF (by decide))) hv hsp0 hret hal hz0 hfr hR

theorem nm_96 {M0 : Word → BitVec 8} {out c s : Word} (hsp : f sp = F) (h18 : f 18 = out)
    (ha0 : (f a0).extractLsb' 0 8 = 0x20) (hO : Out M0 Mf s 164)
    (hS : Slots nmCs F M1 Mf) (hv : NmSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ nmE → f x = g0 x) (hsoF : Sep out 20 F 48) (hsc : Sep out 20 base jsonNextMemberCode.length) :
    WP jsonNextMemberCode base (RPost (g0 ra) (fun M' => MemResF M0 M' out c s 164 none) g0) Mf 0x96 f := by
  refine WP.zero fun hz => ?_
  refine WP.sb nm_at_96 (by (try rsimp); rw [h18]; exact hsc.sub (c := 1) (by decide)) ?_; wn
  rw [h18, ha0]
  refine WP.aluImm nm_at_9a ?_; wn
  have hS' : Slots nmCs F M1 (memStore8 Mf (out + 1) 0x20) :=
    hS.out (out_store8 _ _ _) (slots_sep_out (hsoF.sub (c := 1) (l := 1) (by decide)) (by decide))
  refine nm_9c (by (try rsimp); exact hsp) (by (try rsimp); exact h18) hS' hv hsp0 hret hal hz0 (by keepz hz0)
    (sep_low hsoF (by decide)) (sep_low hsc (by decide)) ?_
  (try rsimp); (try simp only [ev0, ev_mv hz])
  exact ⟨Mf, hO, mem_err Mf out c⟩

end

theorem sep_ke {s F : Word} (hF : s + BitVec.ofNat 32 116 = F) {c w : Nat} (hc : 116 + c + w ≤ 2 ^ 32) :
    Sep (s + BitVec.ofNat 32 84) 32 (F + BitVec.ofNat 32 c) w := by
  subst hF
  have := sep_offsets s (c := 84) (n := 32) (d := 116 + c) (k := w) (Or.inl (by omega)) (by omega) (by omega)
  rwa [← add_ofNat_assoc] at this

theorem nmSepF {s F a : Word} {l c w : Nat} (hF : s + BitVec.ofNat 32 116 = F) (h : Sep s 164 a l)
    (hc : 116 + c + w ≤ 164) : Sep (F + BitVec.ofNat 32 c) w a l := by
  subst hF; rw [add_ofNat_assoc]; exact h.sub hc

theorem nm_ev1 {e : Nat} (h0 : e ≠ 0) (he : e < 2 ^ 32) :
    aluEval .add (BitVec.ofNat 32 e) 0xFFFFFFFF = BitVec.ofNat 32 (e - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [ev_add, BitVec.toNat_add, ofNat_tn he, ofNat_tn (by omega)]
  show (e + 4294967295) % 2 ^ 32 = e - 1
  omega

theorem nm_rb' : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFF83) 0 = !(b.toNat == 125) := by decide

theorem nm_rb0 : ((aluEval .add ((125 : BitVec 8).zeroExtend 32) 0xFFFFFF83).extractLsb' 0 8) = 0 := by decide

section
variable {M M1 Mp : Word → BitVec 8} {base out c s p F : Word} {g g0 : Fin 32 → Word}

/-- The call to `read_item` at `0xb4` and the rest of the function. -/
theorem nm_tail {n pos e v : Nat} (hF : s + BitVec.ofNat 32 116 = F) (hb : base.toNat % 2 = 0)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (halc : c.toNat % 4 = 0) (hn : n < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n ≤ 2 ^ 32) (hpe : pos < e - 1) (hen : e - 1 ≤ n) (hvn : v ≤ n)
    (hrc : RiCode M (base + 0x1DE)) (hrs : RiSep s 164 (base + 0x1DE))
    (hSc : Sep s 164 base jsonNextMemberCode.length) (hSp : Sep s 164 p n) (hso : Sep out 20 s 164)
    (hcs : Sep c 12 s 164) (hoc : Sep out 20 c 12) (hsc : Sep out 20 base jsonNextMemberCode.length)
    (hcc : Sep c 12 base jsonNextMemberCode.length) (hO1 : Out M M1 s 164) (hS : Slots nmCs F Mp M1)
    (hv : NmSaved F g0 Mp) (hv8 : memLoad32 M1 (F + 8) = BitVec.ofNat 32 v)
    (h8 : g 8 = BitVec.ofNat 32 pos) (h9 : g 9 = c) (h18 : g 18 = out) (h19 : g 19 = p)
    (h20 : g 20 = BitVec.ofNat 32 n) (h22 : g 22 = BitVec.ofNat 32 (e - 1)) (hsp : g sp = F)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30) (hret : g0 ra &&& ~~~1 = g0 ra) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ nmE → g x = g0 x) :
    WP jsonNextMemberCode base (RPost (g0 ra) (fun M' => MemResF M M' out c s 164 (memRes p
      ((readItem (memBytes M p n) v).map fun x => some (pos + 1, e - 1 - (pos + 1), v, x.1 - v, x.2)))) g0)
      M1 0xB4 g := by
  refine WP.zero fun hz => ?_
  have halF : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hal (k := 116) (by decide)
  have hF4 : F + 4 = s + BitVec.ofNat 32 120 := by rw [← hF, BitVec.add_assoc]; rfl
  have hd : memBytes M1 p n = memBytes M p n := hO1.bytes hSp
  refine WP.lw nm_at_b4 (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 8) (by decide)) ?_; wn
  refine WP.aluImm nm_at_b6 ?_; wn
  refine WP.alu nm_at_b8 ?_; wn
  refine WP.alu nm_at_ba ?_; wn
  refine WP.callReadItem (tb := base + 0x1DE) (out := F + 4) (s := s) (p := p) (n := n) (pos := v)
    nm_at_bc nm_at_c0 (by simp only [BitVec.add_assoc]; rfl) (even_at base hb 0x1DE (by decide))
    (by decide) (hrc.out hO1 hrs) (hrs.low (by decide)) (by (try rsimp); rw [hsp, ev_add])
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h19)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h20)
    (by (try rsimp); rw [hsp]; exact hv8)
    (by (try rsimp); rw [hsp, hF]) hn (by omega) hal (aligned_add halF (k := 4) (by decide)) (sep_low hSp (by decide))
    (by rw [hF4]; have := sep_offsets s (c := 120) (n := 12) (d := 0) (k := 116) (Or.inr (by decide)) (by decide)
          (by decide); rwa [add_ofNat_zero] at this)
    (by rw [hF4]; exact hrs.ri.sub (by decide)) (sep_low hSc (by decide)) (by rw [hF4]; exact hSc.sub (by decide))
    fun m2 hR => ?_
  rw [hd] at hR
  obtain ⟨Ma, hOa, hCR⟩ := hR
  have hO2 : Out M m2.mem s 164 := hO1.trans ((hOa.mono (by decide)).trans
    (Out.upK (c := 120) hF4.symm hCR.out (by decide)))
  have hcs1 : ∀ c, c ∈ nmCs → 116 + c + 4 ≤ 2 ^ 32 := by decide
  have hcs2 : ∀ c, c ∈ nmCs → (c + 4 ≤ 4 ∨ 4 + 12 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hS2 : Slots nmCs F Mp m2.mem :=
    (hS.out hOa (fun c hc => sep_below116 hF (hcs1 c hc))).out hCR.out (slots_sep F hcs2 (by decide))
  have hsoF : Sep out 20 F 48 := by rw [← hF]; exact hso.subR (by decide)
  have hscF : Sep (c + 8) 4 F 48 := by rw [← hF]; exact (hcs.sub (c := 8) (l := 4) (by decide)).subR (by decide)
  have hcs3 : ∀ c, c ∈ nmCs → c + 4 ≤ 48 := by decide
  refine WP.zero fun hz2 => ?_
  refine WP.lw nm_at_c4 (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 4) (by decide)) ?_; wn
  generalize hri : readItem (memBytes M p n) v = r at hCR ⊢
  rcases r with _ | ⟨ee, a⟩
  · obtain ⟨-, h0, h4⟩ := hCR
    refine WP.branch nm_at_c6 (fun eb => ?_) (fun eb => ?_) <;> wn
    · refine WP.lbu nm_at_e4 ?_; wn
      refine WP.jal nm_at_e8 (by decide) ?_; wn
      have h4' : m2.mem (F + 8) = 32 := by rw [← h4, BitVec.add_assoc]; rfl
      exact nm_96 (by (try rsimp); exact hsp) (by (try rsimp); exact h18)
        (by (try rsimp); rw [hsp, h4', ri_ze]) hO2 hS2 hv hsp0 hret halF hz0 (by keepz hz0) hsoF hsc
    · exfalso; (try rsimp at eb); rw [hsp, h0] at eb; exact absurd eb (by decide)
  · obtain ⟨-, hq, hl, ha⟩ := hCR
    have hbd := readItem_bd hri
    rw [memBytes_length] at hbd
    have hl' : memLoad32 m2.mem (F + 8) = BitVec.ofNat 32 (ee - v) := by rw [← hl, BitVec.add_assoc]; rfl
    have ha' : memLoad32 m2.mem (F + 12) = BitVec.ofNat 32 a := by rw [← ha, BitVec.add_assoc]; rfl
    refine WP.branch nm_at_c6 (fun eb => ?_) (fun eb => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, hq, nx_q0 hp0 hpn (by omega)] at eb; exact absurd eb (by decide)
    refine WP.aluImm nm_at_c8 ?_; wn
    refine WP.lw nm_at_ca (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 12) (by decide)) ?_; wn
    refine WP.lw nm_at_cc (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 8) (by decide)) ?_; wn
    refine WP.sw nm_at_ce (by (try rsimp); rw [h9]; exact aligned_add halc (k := 8) (by decide))
      (by (try rsimp); rw [h9]; exact hcc.sub (c := 8) (by decide)) ?_; wn
    refine WP.aluImm nm_at_d0 ?_; wn
    refine WP.alu nm_at_d2 ?_; wn
    refine WP.alu nm_at_d6 ?_; wn
    refine WP.alu nm_at_d8 ?_; wn
    refine WP.sw nm_at_da (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]; exact aligned_add halo (k := 4) (by decide))
      (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]; exact hsc.sub (c := 4) (by decide)) ?_; wn
    refine WP.sw nm_at_dc (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]; exact aligned_add halo (k := 8) (by decide))
      (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]; exact hsc.sub (c := 8) (by decide)) ?_; wn
    refine WP.sw nm_at_de (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]; exact aligned_add halo (k := 12) (by decide))
      (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]; exact hsc.sub (c := 12) (by decide)) ?_; wn
    refine WP.sw nm_at_e0 (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]; exact aligned_add halo (k := 16) (by decide))
      (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]; exact hsc.sub (c := 16) (by decide)) ?_; wn
    refine WP.jal nm_at_e2 (by decide) ?_; wn
    have hso1 : Sep out 1 base jsonNextMemberCode.length := sep_low hsc (by decide)
    refine WP.sb nm_at_9c (by (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18, add_lit_zero]; exact hso1) ?_
    wn
    have k1 : aluEval .add (BitVec.ofNat 32 pos) 1 = BitVec.ofNat 32 (pos + 1) := by
      rw [ev_add]; exact BitVec.ofNat_add_ofNat ..
    have k2 : aluEval .add (BitVec.ofNat 32 (pos + 1)) p = p + BitVec.ofNat 32 (pos + 1) := by
      rw [ev_add]; exact BitVec.add_comm _ _
    have k3 : aluEval .sub (BitVec.ofNat 32 (e - 1)) (BitVec.ofNat 32 (pos + 1)) =
        BitVec.ofNat 32 (e - 1 - (pos + 1)) := sub_ofNat_le (by omega) (by omega)
    have hq' : memLoad32 m2.mem (F + 4) = p + BitVec.ofNat 32 v := hq
    (try rsimp); (try simp only [ev0, ev_mv hz2])
    rw [h8, h9, h18, h19, h22, hsp, add_lit_zero, hq', hl', ha', k1, k2, k3]
    try rw [show (aluEval .add 0 0).extractLsb' 0 8 = (0 : BitVec 8) by decide]
    try rw [show (0 : Word).extractLsb' 0 8 = (0 : BitVec 8) by decide]
    have hE := mem_ok m2.mem (p + BitVec.ofNat 32 (pos + 1)) (e - 1 - (pos + 1)) (p + BitVec.ofNat 32 v) (ee - v) a
      hoc
    exact nm_epi (by (try rsimp); exact hsp) (hE.slots hS2 (slots_sep_out hsoF hcs3) (slots_sep_out hscF hcs3))
      hv hsp0 hret halF hz0 (by keepz hz0) ⟨m2.mem, hO2, hE⟩

end

section
variable {M M1 Mp : Word → BitVec 8} {base out c s p F : Word} {g g0 : Fin 32 → Word}

theorem nm_92 {M0 : Word → BitVec 8} (hsp : g sp = F) (h18 : g 18 = out) (hO : Out M0 M1 s 164)
    (hS : Slots nmCs F Mp M1) (hv : NmSaved F g0 Mp) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ nmE → g x = g0 x) (hsoF : Sep out 20 F 48) (hsc : Sep out 20 base jsonNextMemberCode.length) :
    WP jsonNextMemberCode base (RPost (g0 ra) (fun M' => MemResF M0 M' out c s 164 none) g0) M1 0x92 g := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm nm_at_92 ?_; wn
  exact nm_96 (by (try rsimp); exact hsp) (by (try rsimp); exact h18)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); decide) hO hS hv hsp0 hret hal hz0 (by keepz hz0) hsoF hsc

theorem nm_ad1 (base : Word) : base + 0x144 + 0xFFFFFFA6 = base + 0x1DE + 0xFFFFFF0C := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem nm_ad2 (base : Word) : base + 0x144 + 0x322 = base + 0x1DE + 0x288 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem nm_ad0 (base : Word) : base + 0xEA = base + 0x1DE + 0xFFFFFF0C := by
  rw [BitVec.add_assoc]; rfl

/-- The call to `key_end` at `0x74` and the rest of the function. -/
theorem nm_key {n pos e : Nat} (hF : s + BitVec.ofNat 32 116 = F) (hb : base.toNat % 2 = 0)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (halc : c.toNat % 4 = 0) (hn : n < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n ≤ 2 ^ 32) (hpe : pos < e - 1) (hen : e - 1 ≤ n)
    (hrc : RiCode M (base + 0x1DE)) (hrs : RiSep s 164 (base + 0x1DE)) (hck : CodeIn M (base + 0x144) jsonKeyEndCode)
    (hks : Sep s 164 (base + 0x144) jsonKeyEndCode.length)
    (hSc : Sep s 164 base jsonNextMemberCode.length) (hSp : Sep s 164 p n) (hso : Sep out 20 s 164)
    (hcs : Sep c 12 s 164) (hoc : Sep out 20 c 12) (hsc : Sep out 20 base jsonNextMemberCode.length)
    (hcc : Sep c 12 base jsonNextMemberCode.length) (hO1 : Out M M1 s 164) (hS : Slots nmCs F Mp M1)
    (hv : NmSaved F g0 Mp) (h8 : g 8 = BitVec.ofNat 32 pos) (h9 : g 9 = c) (h18 : g 18 = out) (h19 : g 19 = p)
    (h20 : g 20 = BitVec.ofNat 32 n) (h22 : g 22 = BitVec.ofNat 32 (e - 1)) (hsp : g sp = F)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30) (hret : g0 ra &&& ~~~1 = g0 ra) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ nmE → g x = g0 x) :
    WP jsonNextMemberCode base (RPost (g0 ra) (fun M' => MemResF M M' out c s 164 (memRes p
      (memberKey (memBytes M p n) pos (e - 1 - (pos + 1))))) g0) M1 0x74 g := by
  refine WP.zero fun hz => ?_
  have halF : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hal (k := 116) (by decide)
  have hF4 : F + 4 = s + BitVec.ofNat 32 120 := by rw [← hF, BitVec.add_assoc]; rfl
  have hd : memBytes M1 p n = memBytes M p n := hO1.bytes hSp
  have rc1 : RiCode M1 (base + 0x1DE) := hrc.out hO1 hrs
  have hsoF : Sep out 20 F 48 := by rw [← hF]; exact hso.subR (by decide)
  have hso4 : Sep (F + 4) 8 (s + BitVec.ofNat 32 84) 32 := by
    rw [hF4]; exact sep_offsets s (c := 120) (n := 8) (d := 84) (k := 32) (Or.inr (by decide)) (by decide) (by decide)
  refine WP.aluImm nm_at_74 ?_; wn
  refine WP.alu nm_at_76 ?_; wn
  refine WP.alu nm_at_78 ?_; wn
  refine WP.alu nm_at_7a ?_; wn
  refine WP.aluImm nm_at_7c ?_; wn
  refine WP.callKeyEnd (tb := base + 0x144) (out := F + 4) (s := s + BitVec.ofNat 32 84) (p := p) (n := n)
    (pos := pos) (cm := false) nm_at_7e nm_at_82 (by simp only [BitVec.add_assoc]; rfl)
    (even_at base hb 0x144 (by decide)) (by decide) (hO1.codeIn hck hks) (by rw [nm_ad1]; exact rc1.se)
    (by rw [nm_ad2]; exact rc1.sw) (by (try rsimp); rw [hsp, ev_add])
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h19)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h20)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h8)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); try rfl)
    (by (try rsimp); rw [hsp, ← hF, BitVec.add_assoc]; rfl) hn (by omega) (aligned_add hal (k := 84) (by decide))
    (aligned_add halF (k := 4) (by decide)) (hks.sub (by decide)) (by rw [nm_ad1]; exact hrs.se.sub (by decide))
    (by rw [nm_ad2]; exact hrs.sw.sub (by decide)) (hSp.sub (by decide))
    hso4
    (by rw [hF4]; exact hks.sub (by decide)) (hSc.sub (by decide)) (by rw [hF4]; exact hSc.sub (by decide))
    fun m2 hR => ?_
  rw [hd] at hR
  obtain ⟨Ma, hOa, hU⟩ := hR
  have hOa' : Out M1 Ma s 164 := Out.upK (c := 84) rfl hOa (by decide)
  have hO2 : Out M m2.mem s 164 := hO1.trans (hOa'.trans (Out.upK (c := 120) hF4.symm hU.out (by decide)))
  have hcs1 : ∀ c, c ∈ nmCs → 116 + c + 4 ≤ 2 ^ 32 := by decide
  have hcs2 : ∀ c, c ∈ nmCs → (c + 4 ≤ 4 ∨ 4 + 8 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hS2 : Slots nmCs F Mp m2.mem :=
    (hS.out hOa (fun c hc => sep_ke hF (hcs1 c hc))).out hU.out (slots_sep F hcs2 (by decide))
  refine WP.zero fun hz2 => ?_
  refine WP.lbu nm_at_86 ?_; wn
  unfold memberKey
  rcases hk : keyEnd false (memBytes M p n) pos with _ | v
  · rw [hk] at hU
    obtain ⟨_, t1, t2⟩ := hU
    have t2' : m2.mem (F + 5) = 0x20 := by
      rw [show F + 5 = F + 4 + 1 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch nm_at_8a (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lbu nm_at_8c ?_; wn
    refine WP.jal nm_at_90 (by decide) ?_; wn
    exact nm_96 (by (try rsimp); exact hsp) (by (try rsimp); exact h18) (by (try rsimp); rw [hsp, t2', ri_ze]) hO2 hS2 hv
      hsp0 hret halF hz0 (by keepz hz0) hsoF hsc
  rw [hk] at hU
  obtain ⟨_, t1, t2⟩ := hU
  have hvn : v ≤ n := by have := keyEnd_le hk; rwa [memBytes_length] at this
  have t2' : memLoad32 m2.mem (F + 8) = BitVec.ofNat 32 v := by
    rw [show F + 8 = F + 4 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
  refine WP.branch nm_at_8a (fun _ => ?_) (fun eb => ?_) <;> wn
  · exact nm_tail hF hb hal halo halc hn hp0 hpn hpe hen hvn hrc hrs hSc hSp hso hcs hoc hsc hcc hO2 hS2 hv t2'
      (by (try rsimp); exact h8) (by (try rsimp); exact h9) (by (try rsimp); exact h18) (by (try rsimp); exact h19)
      (by (try rsimp); exact h20) (by (try rsimp); exact h22) (by (try rsimp); exact hsp) hsp0 hret hz0
      (by keepz hz0)
  · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)

end

end C3.RV32
