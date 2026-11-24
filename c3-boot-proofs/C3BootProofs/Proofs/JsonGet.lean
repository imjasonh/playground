import C3BootProofs.Proofs.JsonNextMember
import C3BootProofs.Proofs.SliceEq
import C3BootProofs.Proofs.MemcpyAny

/-!
# `Value::get`, as compiled

`get` on the object whose `n` bytes are at `p` opens it with `members`,
copies the cursor into its frame with `memcpy`, then calls `next_member`
until a member's key equals the `kl` bytes at `kq` (compared with
`<[u8] as PartialEq>::eq`) or the object ends.

The result has the layout `GetRes` describes: a zero byte at `out`, then the
value's pointer at `out + 4` (zero for `None`) and its length at `out + 8`;
or the byte `1` at `out` and the error byte at `out + 1`, `0x21` when the
value is not an object and `0x20` when it is not valid JSON. The function
saves eight registers in a 64-byte frame, and `next_member` uses 164 more
bytes, so the stack region is the 228 bytes below `sp`. `jsonGet_correct` is
the contract.
-/

namespace C3.Json

/-- `get`'s loop from the member at `pos`, with fuel `k`: `none` for a JSON
error, `some none` when no key matches, and otherwise the value's start and
length. -/
def getFrom (d key : Bytes) : Nat → Nat → Option (Option (Nat × Nat))
  | 0, _ => none
  | k + 1, pos =>
    match nextMember d pos with
    | none => none
    | some none => some none
    | some (some (kp, kl, vp, vl, a)) =>
      if (d.drop kp).take kl = key then some (some (vp, vl)) else getFrom d key k a

/-- A loop result as `get` returns it, with the error byte `0x20`. -/
def getOut : Option (Option (Nat × Nat)) → Except Nat (Option (Nat × Nat))
  | none => .error 0x20
  | some r => .ok r

/-- `Value::get(key)` on the value `d`: the error byte `0x21` when `d` is not
an object, and otherwise the loop's result from the first member. Each
member moves the position forward, so `d.length + 1` is enough fuel. -/
def objGet (d key : Bytes) : Except Nat (Option (Nat × Nat)) :=
  if d.length = 0 ∨ d.getD 0 0 ≠ 123 then .error 0x21 else getOut (getFrom d key (d.length + 1) (skipWs d 1))

theorem skipWs_ge (d : Bytes) (x : Nat) : x ≤ skipWs d x := Nat.le_add_right _ _

theorem wsIn_ge (c : Bool) (d : Bytes) (x : Nat) : x ≤ wsIn c d x := by
  unfold wsIn; split
  · exact Nat.le_refl _
  · exact skipWs_ge d x

theorem keyEnd_gt {c : Bool} {d : Bytes} {pos v : Nat} (h : keyEnd c d pos = some v) : pos < v := by
  unfold keyEnd at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i e he
  split at h
  · cases h
  split at h
  · cases h
  cases h
  have h1 := stringEnd_gt he
  have h2 := wsIn_ge c d e
  have h3 := wsIn_ge c d (wsIn c d e + 1)
  omega

theorem readItem_after {d : Bytes} {v : Nat} {x : Nat × Nat} (h : readItem d v = some x) : x.1 ≤ x.2 := by
  unfold readItem at h
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.mp h
  unfold itemTail
  split
  · exact Nat.le_trans (skipWs_ge d e) (Nat.le_trans (Nat.le_succ _) (skipWs_ge d _))
  · exact skipWs_ge d e

theorem readItem_after_le {d : Bytes} {v : Nat} {x : Nat × Nat} (h : readItem d v = some x) :
    x.2 ≤ d.length := by
  have hb := (C3.RV32.readItem_bd h).2
  unfold readItem at h
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.mp h
  have he : e ≤ d.length := by unfold itemTail at hb; split at hb <;> exact hb
  unfold itemTail
  split
  · rename_i hc
    have := skipWs_le d (skipWs d e + 1)
    exact Nat.le_trans this (by omega)
  · have := skipWs_le d e
    exact Nat.le_trans this (by omega)

/-- A member starts before the end, ends after its start and inside the
object, and has its key inside the object. -/
theorem nextMember_lt {d : Bytes} {pos kp kl vp vl a : Nat}
    (h : nextMember d pos = some (some (kp, kl, vp, vl, a))) :
    pos < d.length ∧ pos < a ∧ kp + kl ≤ d.length ∧ a ≤ d.length := by
  unfold nextMember at h
  split at h
  · cases h
  cases hs : stringEnd true d pos with
  | none => rw [hs, Option.bind_none] at h; cases h
  | some e =>
    rw [hs, Option.bind_some] at h
    have hlt : pos < d.length := by
      apply Nat.lt_of_not_le; intro hle; rw [stringEnd_none hle] at hs; cases hs
    unfold memberTail at h
    split at h
    · cases h
    rename_i hc
    have hle := stringEnd_le hs
    unfold memberKey at h
    cases hk : keyEnd false d pos with
    | none => rw [hk] at h; cases h
    | some v =>
      simp only [hk] at h
      cases hr : readItem d v with
      | none => rw [hr] at h; cases h
      | some x =>
        rw [hr] at h
        cases h
        have h1 := keyEnd_gt hk
        have h2 := C3.RV32.readItem_bd hr
        have h3 := readItem_after hr
        have hc1 : ¬e - 1 ≤ pos := fun h' => hc (Or.inr (Or.inl h'))
        have hc2 : ¬d.length < e - 1 := fun h' => hc (Or.inr (Or.inr h'))
        have h4 := readItem_after_le hr
        exact ⟨hlt, by omega, by omega, h4⟩

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem gt_at_0 : fetchRel jsonGetCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem gt_at_2 : fetchRel jsonGetCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem gt_at_4 : fetchRel jsonGetCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem gt_at_6 : fetchRel jsonGetCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem gt_at_8 : fetchRel jsonGetCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem gt_at_a : fetchRel jsonGetCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem gt_at_c : fetchRel jsonGetCode 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem gt_at_e : fetchRel jsonGetCode 0xE = some (.store .sw sp (21 : Fin 32) 0x24, 2) := by decide
theorem gt_at_10 : fetchRel jsonGetCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x20, 2) := by decide
theorem gt_at_12 : fetchRel jsonGetCode 0x12 = some (.alu .add (21 : Fin 32) x0 a4, 2) := by decide
theorem gt_at_14 : fetchRel jsonGetCode 0x14 = some (.alu .add (22 : Fin 32) x0 a3, 2) := by decide
theorem gt_at_16 : fetchRel jsonGetCode 0x16 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem gt_at_18 : fetchRel jsonGetCode 0x18 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem gt_at_1a : fetchRel jsonGetCode 0x1A = some (.auipc ra 0x0, 4) := by decide
theorem gt_at_1e : fetchRel jsonGetCode 0x1E = some (.jalr ra ra 0x8C, 4) := by decide
theorem gt_at_22 : fetchRel jsonGetCode 0x22 = some (.load .lw (20 : Fin 32) sp 0xC, 2) := by decide
theorem gt_at_24 : fetchRel jsonGetCode 0x24 = some (.load .lbu (19 : Fin 32) sp 0x10, 4) := by decide
theorem gt_at_28 : fetchRel jsonGetCode 0x28 = some (.branch .beq (20 : Fin 32) x0 0x50, 4) := by decide
theorem gt_at_2c : fetchRel jsonGetCode 0x2C = some (.aluImm .add a1 sp 0x11, 4) := by decide
theorem gt_at_30 : fetchRel jsonGetCode 0x30 = some (.aluImm .add a0 sp 0x5, 4) := by decide
theorem gt_at_34 : fetchRel jsonGetCode 0x34 = some (.aluImm .add a2 x0 0x7, 2) := by decide
theorem gt_at_36 : fetchRel jsonGetCode 0x36 = some (.auipc ra 0xC000, 4) := by decide
theorem gt_at_3a : fetchRel jsonGetCode 0x3A = some (.jalr ra ra 0xFFFFFFA4, 4) := by decide
theorem gt_at_3e : fetchRel jsonGetCode 0x3E = some (.store .sw sp (20 : Fin 32) 0x0, 2) := by decide
theorem gt_at_40 : fetchRel jsonGetCode 0x40 = some (.store .sb sp (19 : Fin 32) 0x4, 4) := by decide
theorem gt_at_44 : fetchRel jsonGetCode 0x44 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem gt_at_46 : fetchRel jsonGetCode 0x46 = some (.alu .add a1 x0 sp, 2) := by decide
theorem gt_at_48 : fetchRel jsonGetCode 0x48 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem gt_at_4c : fetchRel jsonGetCode 0x4C = some (.jalr ra ra 0x3F0, 4) := by decide
theorem gt_at_50 : fetchRel jsonGetCode 0x50 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem gt_at_54 : fetchRel jsonGetCode 0x54 = some (.branch .bne a0 x0 0x2A, 2) := by decide
theorem gt_at_56 : fetchRel jsonGetCode 0x56 = some (.load .lw a0 sp 0x10, 2) := by decide
theorem gt_at_58 : fetchRel jsonGetCode 0x58 = some (.branch .beq a0 x0 0x32, 2) := by decide
theorem gt_at_5a : fetchRel jsonGetCode 0x5A = some (.load .lw a1 sp 0x14, 2) := by decide
theorem gt_at_5c : fetchRel jsonGetCode 0x5C = some (.load .lw (9 : Fin 32) sp 0x18, 2) := by decide
theorem gt_at_5e : fetchRel jsonGetCode 0x5E = some (.load .lw (8 : Fin 32) sp 0x1C, 2) := by decide
theorem gt_at_60 : fetchRel jsonGetCode 0x60 = some (.alu .add a2 x0 (22 : Fin 32), 2) := by decide
theorem gt_at_62 : fetchRel jsonGetCode 0x62 = some (.alu .add a3 x0 (21 : Fin 32), 2) := by decide
theorem gt_at_64 : fetchRel jsonGetCode 0x64 = some (.auipc ra 0x0, 4) := by decide
theorem gt_at_68 : fetchRel jsonGetCode 0x68 = some (.jalr ra ra 0xFFFFFF86, 4) := by decide
theorem gt_at_6c : fetchRel jsonGetCode 0x6C = some (.branch .beq a0 x0 0xFFFFFFD8, 2) := by decide
theorem gt_at_6e : fetchRel jsonGetCode 0x6E = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem gt_at_70 : fetchRel jsonGetCode 0x70 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem gt_at_72 : fetchRel jsonGetCode 0x72 = some (.store .sw a1 (9 : Fin 32) 0x4, 2) := by decide
theorem gt_at_74 : fetchRel jsonGetCode 0x74 = some (.store .sw a1 (8 : Fin 32) 0x8, 2) := by decide
theorem gt_at_76 : fetchRel jsonGetCode 0x76 = some (.jal x0 0x18, 2) := by decide
theorem gt_at_78 : fetchRel jsonGetCode 0x78 = some (.store .sb (18 : Fin 32) (19 : Fin 32) 0x1, 4) := by decide
theorem gt_at_7c : fetchRel jsonGetCode 0x7C = some (.jal x0 0xA, 2) := by decide
theorem gt_at_7e : fetchRel jsonGetCode 0x7E = some (.load .lbu a0 sp 0xD, 4) := by decide
theorem gt_at_82 : fetchRel jsonGetCode 0x82 = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem gt_at_86 : fetchRel jsonGetCode 0x86 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem gt_at_88 : fetchRel jsonGetCode 0x88 = some (.jal x0 0x6, 2) := by decide
theorem gt_at_8a : fetchRel jsonGetCode 0x8A = some (.store .sw (18 : Fin 32) x0 0x4, 4) := by decide
theorem gt_at_8e : fetchRel jsonGetCode 0x8E = some (.store .sb (18 : Fin 32) a0 0x0, 4) := by decide
theorem gt_at_92 : fetchRel jsonGetCode 0x92 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem gt_at_94 : fetchRel jsonGetCode 0x94 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem gt_at_96 : fetchRel jsonGetCode 0x96 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem gt_at_98 : fetchRel jsonGetCode 0x98 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem gt_at_9a : fetchRel jsonGetCode 0x9A = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem gt_at_9c : fetchRel jsonGetCode 0x9C = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem gt_at_9e : fetchRel jsonGetCode 0x9E = some (.load .lw (21 : Fin 32) sp 0x24, 2) := by decide
theorem gt_at_a0 : fetchRel jsonGetCode 0xA0 = some (.load .lw (22 : Fin 32) sp 0x20, 2) := by decide
theorem gt_at_a2 : fetchRel jsonGetCode 0xA2 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem gt_at_a4 : fetchRel jsonGetCode 0xA4 = some (.jalr x0 ra 0x0, 2) := by decide

/-- `out` holds `r` as a `Result<Option<Value>, TufError>`, and only the 12
bytes at `out` changed. -/
def GetRes (M M' : Word → BitVec 8) (out : Word) : Except Nat (Option (Word × Nat)) → Prop
  | .error e => (∀ x, Sep x 1 out 12 → M' x = M x) ∧ M' out = 1 ∧ M' (out + 1) = BitVec.ofNat 8 e
  | .ok none => (∀ x, Sep x 1 out 12 → M' x = M x) ∧ M' out = 0 ∧ memLoad32 M' (out + 4) = 0
  | .ok (some (q, l)) => (∀ x, Sep x 1 out 12 → M' x = M x) ∧ M' out = 0 ∧
      memLoad32 M' (out + 4) = q ∧ memLoad32 M' (out + 8) = BitVec.ofNat 32 l

/-- `GetRes` after a function that may also change the `k` bytes at `s`. -/
def GetResF (M M' : Word → BitVec 8) (out s : Word) (k : Nat) (r : Except Nat (Option (Word × Nat))) : Prop :=
  ∃ M1, Out M M1 s k ∧ GetRes M1 M' out r

/-- The word-level result of `get` on the value at `p`. -/
def getRes (p : Word) (r : Except Nat (Option (Nat × Nat))) : Except Nat (Option (Word × Nat)) :=
  r.map (Option.map fun x => (p + BitVec.ofNat 32 x.1, x.2))

theorem GetRes.out {M M' : Word → BitVec 8} {out : Word} {r : Except Nat (Option (Word × Nat))}
    (h : GetRes M M' out r) : Out M M' out 12 := by
  rcases r with _ | _ | ⟨_, _⟩
  · exact h.1
  · exact h.1
  · exact h.1

theorem get_err (M : Word → BitVec 8) (out : Word) (e : Nat) :
    GetRes M (memStore8 (memStore8 M (out + 1) (BitVec.ofNat 8 e)) out 1) out (.error e) := by
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 1) x h0]
    exact (out_store8 _ (out + 1) _) x (hx.subR (c := 1) (l := 1) (by decide))
  · rw [memStore8_ne (ne_add_one out), memStore8_same]

theorem get_none (M : Word → BitVec 8) (out : Word) :
    GetRes M (memStore8 (memStore32 M (out + 4) 0) out 0) out (.ok none) := by
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 0) x h0]
    exact (out_store32 _ (out + 4) 0) x (hx.subR (c := 4) (l := 4) (by decide))
  · exact ((out_store8 _ out 0).load32 (sep_o4 out (d := 4) (by decide) (by decide))).trans
      (memLoad32_store32_same _ _ _)

theorem get_some (M : Word → BitVec 8) (out q : Word) (l : Nat) :
    GetRes M (memStore8 (memStore32 (memStore32 M (out + 4) q) (out + 8) (BitVec.ofNat 32 l)) out 0) out
      (.ok (some (q, l))) := by
  have s48 : Sep (out + BitVec.ofNat 32 4) 4 (out + BitVec.ofNat 32 8) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 0) x h0, (out_store32 _ (out + 8) _) x (hx.subR (c := 8) (l := 4) (by decide))]
    exact (out_store32 _ (out + 4) _) x (hx.subR (c := 4) (l := 4) (by decide))
  · exact ((out_store8 _ out 0).load32 (sep_o4 out (d := 4) (by decide) (by decide))).trans <|
      (memLoad32_store32_sep s48.symm).trans (memLoad32_store32_same _ _ _)
  · exact ((out_store8 _ out 0).load32 (sep_o4 out (d := 8) (by decide) (by decide))).trans
      (memLoad32_store32_same _ _ _)

/-- Four bytes at `a` equal to the four at `b` load the same word. -/
theorem memLoad32_shift {M M' : Word → BitVec 8} {a b : Word}
    (h : ∀ j, j < 4 → M' (a + BitVec.ofNat 32 j) = M (b + BitVec.ofNat 32 j)) :
    memLoad32 M' a = memLoad32 M b := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at h0
  rw [show a + 1 = a + BitVec.ofNat 32 1 from rfl, show a + 2 = a + BitVec.ofNat 32 2 from rfl,
    show a + 3 = a + BitVec.ofNat 32 3 from rfl, show b + 1 = b + BitVec.ofNat 32 1 from rfl,
    show b + 2 = b + BitVec.ofNat 32 2 from rfl, show b + 3 = b + BitVec.ofNat 32 3 from rfl,
    h0, h 1 (by decide), h 2 (by decide), h 3 (by decide)]

theorem memBytes_slice {M : Word → BitVec 8} {p : Word} {n h l : Nat} (hl : h + l ≤ n) :
    ((memBytes M p n).drop h).take l = memBytes M (p + BitVec.ofNat 32 h) l := by
  unfold memBytes
  rw [← List.map_drop, ← List.map_take]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, List.length_range]; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [add_ofNat_assoc]

theorem MemRes.codeIn {M M' : Word → BitVec 8} {out c b : Word} {code : List Nat}
    {r : Option (Option (Word × Nat × Word × Nat × Nat))} (h : MemRes M M' out c r) (hc : CodeIn M b code)
    (ho : Sep out 20 b code.length) (hcb : Sep (c + 8) 4 b code.length) : CodeIn M' b code :=
  fun i hi => by rw [h.out (sep_pt ho hi) (sep_pt hcb hi)]; exact hc i hi

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `members()` on the `n` bytes at `p` with the code at `tb`. -/
theorem WP.callMembers {hi lo tb p out s : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonMembersCode) (hcw : CodeIn M (tb + 0xFFFFF7F8) jsonSkipWsCode)
    (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (hsp : f sp = s + BitVec.ofNat 32 16)
    (hn : n < 2 ^ 32) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hSc : Sep s 16 tb jsonMembersCode.length) (hSw : Sep s 16 (tb + 0xFFFFF7F8) jsonSkipWsCode.length)
    (hSp : Sep s 16 p n) (hso : Sep out 12 s 16) (hsc : Sep out 12 tb jsonMembersCode.length)
    (hSb : Sep s 16 base code.length) (hsb : Sep out 12 base code.length)
    (k : ∀ m2 : Machine, CurResF M m2.mem out s 16 0x21 (curOpen 123 p (memBytes M p n)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => CurResF M m2.mem out s 16 0x21 (curOpen 123 p (memBytes M p n)))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hU⟩ := hP
      exact hU.out.codeIn (hO.codeIn hc hSb) hsb) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonMembers_correct m1 (base := tb) (out := out) (s := s) (p := p) (n := n)
    htb (by rw [hmem1]; exact hct) (by rw [hmem1]; exact hcw) hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact hsp) hn hal halo
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    hSc hSw hSp hso hsc
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

/-- A call to `memcpy(dst, src, N)` through the stub at `tb`, whose frame is
the 16 bytes at `F`. -/
theorem WP.callMemcpy {hi lo tb dst src F : Word} {N : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hcs : CodeIn M tb memcpyStubCode) (E : McEnv M (tb + 8) dst src F N)
    (h0 : f a0 = dst) (ha1 : f a1 = src) (ha2 : f a2 = BitVec.ofNat 32 N) (hsp : f sp = F + 16)
    (hFb : Sep F 16 base code.length) (hDb : Sep dst N base code.length)
    (k : ∀ m2 : Machine, Out (copyBytes M dst src N) m2.mem F 16 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob) (P := fun m2 => Out (copyBytes M dst src N) m2.mem F 16)
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.codeIn (fun i hi => by
      rw [copyBytes_sep (sep_pt hDb hi).symm (Nat.le_refl _)]; exact hc i hi) hFb) k
  have hsp1 : reg m1 sp = F + 16 := by rw [hreg1]; rsimp; exact hsp
  have hF : reg m1 sp + 0xFFFFFFF0 = F := by
    rw [hsp1, BitVec.add_assoc, show (16 : Word) + 0xFFFFFFF0 = 0 by decide, add_lit_zero]
  obtain ⟨m2, c2, pc2, sp2, -, hmem, hfr⟩ := memcpy_correct m1 tb (base + BitVec.ofNat 32 (off + 8)) dst src N
    (fun i hi => by rw [hmem1]; exact hcs i hi) htb hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev)) (by rw [hF, hmem1]; exact E)
  refine ⟨m2, c2, pc2, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hmem x (by rw [hF]; exact hx.symm), hmem1]
  · by_cases hs : x = sp
    · subst hs; exact sp2
    exact hfr x (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
      (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
      (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
      (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
      (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide)) hs

/-- A call to `next_member` on the cursor at `c` with the code at `tb`. -/
theorem WP.callNextMember {hi lo tb out c s p : Word} {n pos : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonNextMemberCode) (hrc : RiCode M (tb + 0x1DE))
    (hck : CodeIn M (tb + 0x144) jsonKeyEndCode) (h0 : f a0 = out) (ha1 : f a1 = c)
    (hsp : f sp = s + BitVec.ofNat 32 164) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (halc : c.toNat % 4 = 0) (hmp : memLoad32 M c = p) (hmn : memLoad32 M (c + 4) = BitVec.ofNat 32 n)
    (hmq : memLoad32 M (c + 8) = BitVec.ofNat 32 pos) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n ≤ 2 ^ 32) (hrs : RiSep s 164 (tb + 0x1DE))
    (hks : Sep s 164 (tb + 0x144) jsonKeyEndCode.length)
    (hSc : Sep s 164 tb jsonNextMemberCode.length) (hSp : Sep s 164 p n) (hso : Sep out 20 s 164)
    (hcs : Sep c 12 s 164) (hoc : Sep out 20 c 12) (hsc : Sep out 20 tb jsonNextMemberCode.length)
    (hcc : Sep c 12 tb jsonNextMemberCode.length) (hSb : Sep s 164 base code.length)
    (hsb : Sep out 20 base code.length) (hcb : Sep c 12 base code.length)
    (k : ∀ m2 : Machine, MemResF M m2.mem out c s 164 (memRes p (nextMember (memBytes M p n) pos)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => MemResF M m2.mem out c s 164 (memRes p (nextMember (memBytes M p n) pos)))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hR⟩ := hP
      exact hR.codeIn (hO.codeIn hc hSb) hsb (hcb.sub (c := 8) (l := 4) (by decide))) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := jsonNextMember_correct m1 (base := tb) (out := out) (c := c) (s := s) (p := p)
    (n := n) (pos := pos) htb (by rw [hmem1]; exact hct) (by rw [hmem1]; exact hrc) (by rw [hmem1]; exact hck)
    hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact hsp)
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    hal halo halc (by rw [hmem1]; exact hmp) (by rw [hmem1]; exact hmn) (by rw [hmem1]; exact hmq) hn hpos hp0 hpn
    hrs hks hSc hSp hso hcs hoc hsc hcc
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

/-- A call to `<[u8] as PartialEq>::eq` on the `pl` bytes at `p` and the
`ql` bytes at `q`, with the code at `tb`. -/
theorem WP.callSliceEq {hi lo tb p q : Word} {pl ql : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hc : CodeIn M tb sliceEqCode) (he : CodeIn M (tb + 0xFFFFEBAA) equalSameLengthCode)
    (hm : CodeIn M (tb + 0xBF68) memcmpCode) (h0 : f a0 = p) (ha1 : f a1 = BitVec.ofNat 32 pl)
    (ha2 : f a2 = q) (ha3 : f a3 = BitVec.ofNat 32 ql) (hpl : pl < 2 ^ 32) (hql : ql < 2 ^ 32)
    (hal : (f sp).toNat % 4 = 0)
    (sSE : Sep (f sp + 0xFFFFFFFC) 4 (tb + 0xFFFFEBAA) equalSameLengthCode.length)
    (sSM : Sep (f sp + 0xFFFFFFFC) 4 (tb + 0xBF68) memcmpCode.length)
    (sSP : Sep (f sp + 0xFFFFFFFC) 4 p pl) (sSQ : Sep (f sp + 0xFFFFFFFC) 4 q ql)
    (hSb : Sep (f sp + 0xFFFFFFFC) 4 base code.length)
    (k : ∀ m2 : Machine, reg m2 a0 = (if memBytes M p pl = memBytes M q ql then 1 else 0) →
      Out M m2.mem (f sp + 0xFFFFFFFC) 4 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => reg m2 a0 = (if memBytes M p pl = memBytes M q ql then 1 else 0) ∧
      Out M m2.mem (f sp + 0xFFFFFFFC) 4)
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc hSb) (fun m2 hP => k m2 hP.1 hP.2)
  have hsp1 : reg m1 sp = f sp := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, ha0, hfr, hmem⟩ := sliceEq_correct m1 (base := tb) (p := p) (q := q) (pl := pl) (ql := ql)
    htb (by rw [hmem1]; exact hc) (by rw [hmem1]; exact he) (by rw [hmem1]; exact hm) hpc1
    (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (by rw [hreg1]; rsimp; exact ha3) hpl hql (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev)) (by rw [hsp1]; exact hal) (by rw [hsp1]; exact sSE)
    (by rw [hsp1]; exact sSM) (by rw [hsp1]; exact sSP) (by rw [hsp1]; exact sSQ)
  refine ⟨m2, c2, pc2, ⟨by rw [ha0, hmem1], fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [hmem x (by rw [hsp1]; exact hx.symm), hmem1]
  · exact hfr x (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
      (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide)) (fun h => hx (by subst h; decide))
      (fun h => hx (by subst h; decide))

end

/-- The code `get` runs, at its offsets from `get`'s address `b`. -/
structure GetCode (M : Word → BitVec 8) (b : Word) : Prop where
  get : CodeIn M b jsonGetCode
  me : CodeIn M (b + 0xA6) jsonMembersCode
  stub : CodeIn M (b + 0xBFDA) memcpyStubCode
  mc : CodeIn M (b + 0xBFE2) memcpyBodyCode
  nm : CodeIn M (b + 0xFFFFF438) jsonNextMemberCode
  ke : CodeIn M (b + 0xFFFFF57C) jsonKeyEndCode
  eq : CodeIn M (b + 0xFFFFFFEA) sliceEqCode
  ri : RiCode M (b + 0xFFFFF616)

/-- The `k` bytes at `s` are apart from `GetCode M b`. -/
structure GetSep (s : Word) (k : Nat) (b : Word) : Prop where
  get : Sep s k b jsonGetCode.length
  me : Sep s k (b + 0xA6) jsonMembersCode.length
  stub : Sep s k (b + 0xBFDA) memcpyStubCode.length
  mc : Sep s k (b + 0xBFE2) memcpyBodyCode.length
  nm : Sep s k (b + 0xFFFFF438) jsonNextMemberCode.length
  ke : Sep s k (b + 0xFFFFF57C) jsonKeyEndCode.length
  eq : Sep s k (b + 0xFFFFFFEA) sliceEqCode.length
  ri : RiSep s k (b + 0xFFFFF616)

theorem GetSep.sub {s b : Word} {k : Nat} (h : GetSep s k b) {c l : Nat} (hcl : c + l ≤ k) :
    GetSep (s + BitVec.ofNat 32 c) l b :=
  ⟨h.get.sub hcl, h.me.sub hcl, h.stub.sub hcl, h.mc.sub hcl, h.nm.sub hcl, h.ke.sub hcl, h.eq.sub hcl,
    h.ri.sub hcl⟩

theorem GetSep.low {s b : Word} {k : Nat} (h : GetSep s k b) {l : Nat} (hl : l ≤ k) : GetSep s l b := by
  have := h.sub (c := 0) (l := l) (by omega)
  rwa [add_ofNat_zero] at this

theorem GetCode.out {M M' : Word → BitVec 8} {b s : Word} {k : Nat} (h : GetCode M b) (hO : Out M M' s k)
    (hs : GetSep s k b) : GetCode M' b :=
  ⟨hO.codeIn h.get hs.get, hO.codeIn h.me hs.me, hO.codeIn h.stub hs.stub, hO.codeIn h.mc hs.mc,
    hO.codeIn h.nm hs.nm, hO.codeIn h.ke hs.ke, hO.codeIn h.eq hs.eq, h.ri.out hO hs.ri⟩

theorem gt_ad_sw (b : Word) : b + 0xA6 + 0xFFFFF7F8 = b + 0xFFFFF616 + 0x288 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem gt_ad_mc (b : Word) : b + 0xBFDA + 8 = b + 0xBFE2 := by rw [BitVec.add_assoc]; rfl

theorem gt_ad_ri (b : Word) : b + 0xFFFFF438 + 0x1DE = b + 0xFFFFF616 := by rw [BitVec.add_assoc]; rfl

theorem gt_ad_ke (b : Word) : b + 0xFFFFF438 + 0x144 = b + 0xFFFFF57C := by rw [BitVec.add_assoc]; rfl

theorem gt_ad_es (b : Word) : b + 0xFFFFFFEA + 0xFFFFEBAA = b + 0xFFFFF616 + 0xFFFFF57E := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem gt_ad_mm (b : Word) : b + 0xFFFFFFEA + 0xBF68 = b + 0xFFFFF616 + 0xC93C := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

/-- The registers `get` changes before its epilogue restores the saved ones. -/
abbrev gtE : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21, 22]

abbrev gtCs : List Nat := [0x20, 0x24, 0x28, 0x2C, 0x30, 0x34, 0x38, 0x3C]

/-- The saved registers in the frame at `F`. -/
def GtSaved (F : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (F + BitVec.ofNat 32 0x3C) = g0 ra ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x38) = g0 8 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x34) = g0 9 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x30) = g0 18 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x2C) = g0 19 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x28) = g0 20 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x24) = g0 21 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x20) = g0 22

/-- Memory after the prologue. -/
def gtM1 (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
    (F + 0x3C) (g0 ra)) (F + 0x38) (g0 8)) (F + 0x34) (g0 9)) (F + 0x30) (g0 18)) (F + 0x2C) (g0 19))
    (F + 0x28) (g0 20)) (F + 0x24) (g0 21)) (F + 0x20) (g0 22)

theorem gt_ld {M : Word → BitVec 8} {F v : Word} (c : Nat) (hc : c ∈ gtCs) (ds : List Nat)
    (hd : ∀ d, d ∈ ds → c + 4 ≤ d ∨ d + 4 ≤ c) (hds : ∀ d, d ∈ ds → d + 4 ≤ 64)
    (h : memLoad32 M (F + BitVec.ofNat 32 c) = v) (ws : List Word) :
    memLoad32 ((ds.zip ws).foldl (fun M' x => memStore32 M' (F + BitVec.ofNat 32 x.1) x.2) M)
      (F + BitVec.ofNat 32 c) = v := by
  induction ds generalizing M ws with
  | nil => exact h
  | cons d ds ih =>
    cases ws with
    | nil => exact h
    | cons w ws =>
      have h1 : c + 4 ≤ 64 := by
        simp only [gtCs, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ih (fun d hd' => hd d (List.mem_cons_of_mem _ hd')) (fun d hd' => hds d (List.mem_cons_of_mem _ hd'))
        (ld_skip c d (hd d (List.mem_cons_self ..)) (by omega) (by have := hds d (List.mem_cons_self ..); omega) h) ws

theorem gt_pro (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) :
    Out M (gtM1 M F g0) F 64 ∧ GtSaved F g0 (gtM1 M F g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((((out_store32 _ _ _).widen (d := 0x3C) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x38) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x34) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x30) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x2C) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x28) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x24) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x20) (by decide)))
  · exact gt_ld 0x3C (by decide) [0x38, 0x34, 0x30, 0x2C, 0x28, 0x24, 0x20] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 8, g0 9, g0 18, g0 19, g0 20, g0 21, g0 22]
  · exact gt_ld 0x38 (by decide) [0x34, 0x30, 0x2C, 0x28, 0x24, 0x20] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 9, g0 18, g0 19, g0 20, g0 21, g0 22]
  · exact gt_ld 0x34 (by decide) [0x30, 0x2C, 0x28, 0x24, 0x20] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 18, g0 19, g0 20, g0 21, g0 22]
  · exact gt_ld 0x30 (by decide) [0x2C, 0x28, 0x24, 0x20] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 19, g0 20, g0 21, g0 22]
  · exact gt_ld 0x2C (by decide) [0x28, 0x24, 0x20] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 20, g0 21, g0 22]
  · exact gt_ld 0x28 (by decide) [0x24, 0x20] (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 21, g0 22]
  · exact gt_ld 0x24 (by decide) [0x20] (by decide) (by decide) (memLoad32_store32_same _ _ _) [g0 22]
  · exact memLoad32_store32_same _ _ _

section
variable {M1 Mf : Word → BitVec 8} {base F : Word} {f g0 : Fin 32 → Word}

theorem gt_epi {R : (Word → BitVec 8) → Prop} (hsp : f sp = F)
    (hS : Slots gtCs F M1 Mf) (hv : GtSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ gtE → f x = g0 x) (hR : R Mf) :
    WP jsonGetCode base (RPost (g0 ra) R g0) Mf 0x92 f := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := hv
  have e1 : memLoad32 Mf (F + 0x3C) = g0 ra := (hS 0x3C (by decide)).trans v1
  have e2 : memLoad32 Mf (F + 0x38) = g0 8 := (hS 0x38 (by decide)).trans v2
  have e3 : memLoad32 Mf (F + 0x34) = g0 9 := (hS 0x34 (by decide)).trans v3
  have e4 : memLoad32 Mf (F + 0x30) = g0 18 := (hS 0x30 (by decide)).trans v4
  have e5 : memLoad32 Mf (F + 0x2C) = g0 19 := (hS 0x2C (by decide)).trans v5
  have e6 : memLoad32 Mf (F + 0x28) = g0 20 := (hS 0x28 (by decide)).trans v6
  have e7 : memLoad32 Mf (F + 0x24) = g0 21 := (hS 0x24 (by decide)).trans v7
  have e8 : memLoad32 Mf (F + 0x20) = g0 22 := (hS 0x20 (by decide)).trans v8
  refine WP.lw gt_at_92 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x3C) (by decide)) ?_; wn
  refine WP.lw gt_at_94 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x38) (by decide)) ?_; wn
  refine WP.lw gt_at_96 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x34) (by decide)) ?_; wn
  refine WP.lw gt_at_98 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x30) (by decide)) ?_; wn
  refine WP.lw gt_at_9a (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x2C) (by decide)) ?_; wn
  refine WP.lw gt_at_9c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x28) (by decide)) ?_; wn
  refine WP.lw gt_at_9e (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x24) (by decide)) ?_; wn
  refine WP.lw gt_at_a0 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x20) (by decide)) ?_; wn
  refine WP.aluImm gt_at_a2 ?_; wn
  refine WP.ret gt_at_a4 ⟨?_, hR, ?_⟩
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

theorem gt_8e {R : (Word → BitVec 8) → Prop} {out : Word} (hsp : f sp = F) (h18 : f 18 = out)
    (hS : Slots gtCs F M1 Mf) (hv : GtSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ gtE → f x = g0 x) (hsoF : Sep out 1 F 64) (hso1 : Sep out 1 base jsonGetCode.length)
    (hR : R (memStore8 Mf out ((f a0).extractLsb' 0 8))) :
    WP jsonGetCode base (RPost (g0 ra) R g0) Mf 0x8E f := by
  refine WP.sb gt_at_8e (by (try rsimp); rw [h18, add_lit_zero]; exact hso1) ?_; wn
  rw [h18, add_lit_zero]
  exact gt_epi hsp (hS.out (out_store8 _ _ _) (slots_sep_out hsoF (by decide))) hv hsp0 hret hal hz0 hfr hR

end

theorem gt_below {s F : Word} (hF : s + BitVec.ofNat 32 164 = F) {c w : Nat} (hc : 164 + c + w ≤ 2 ^ 32) :
    Sep s 164 (F + BitVec.ofNat 32 c) w := by
  subst hF
  have := sep_offsets s (c := 0) (n := 164) (d := 164 + c) (k := w) (Or.inl (by omega)) (by omega) (by omega)
  rwa [add_ofNat_zero, ← add_ofNat_assoc] at this

theorem gtSepF {s F a : Word} {l c w : Nat} (hF : s + BitVec.ofNat 32 164 = F) (h : Sep s 228 a l)
    (hc : 164 + c + w ≤ 228) : Sep (F + BitVec.ofNat 32 c) w a l := by
  subst hF; rw [add_ofNat_assoc]; exact h.sub hc

theorem gtSepF0 {s F a : Word} {l : Nat} (hF : s + BitVec.ofNat 32 164 = F) (h : Sep s 228 a l) :
    Sep F 12 a l := by
  have := gtSepF (c := 0) (w := 12) hF h (by decide); rwa [add_ofNat_zero] at this

/-- `next_member` keeps the cursor's first two words. -/
theorem MemRes.keep {M M' : Word → BitVec 8} {F : Word} {r : Option (Option (Word × Nat × Word × Nat × Nat))}
    (h : MemRes M M' (F + 0xC) F r) {c : Nat} (hc : c + 4 ≤ 8) :
    memLoad32 M' (F + BitVec.ofNat 32 c) = memLoad32 M (F + BitVec.ofNat 32 c) := by
  refine memLoad32_congr fun j hj => h.out ?_ ?_
  · have := sep_offsets F (c := c + j) (n := 1) (d := 12) (k := 20) (Or.inl (by omega)) (by omega) (by decide)
    rw [add_ofNat_assoc]; exact this
  · have := sep_offsets F (c := c + j) (n := 1) (d := 8) (k := 4) (Or.inl (by omega)) (by omega) (by decide)
    rw [add_ofNat_assoc]; exact this

section
variable {Mp : Word → BitVec 8} {base out s p kq F : Word} {g0 : Fin 32 → Word} {n kl : Nat}

/-- The loop at `0x44`, by fuel. -/
theorem gt_loop (M0 : Word → BitVec 8) (hF : s + BitVec.ofNat 32 164 = F) (hb : base.toNat % 2 = 0)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hn : n < 2 ^ 32) (hkl : kl < 2 ^ 32) (hp0 : p.toNat ≠ 0)
    (hpn : p.toNat + n < 2 ^ 32) (hcode : GetCode M0 base) (hgs : GetSep s 228 base) (hSp : Sep s 228 p n)
    (hSk : Sep s 228 kq kl) (hso : Sep out 12 s 228) (hsc : Sep out 12 base jsonGetCode.length)
    (hv : GtSaved F g0 Mp) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hz0 : g0 0 = 0) :
    ∀ k pos (M : Word → BitVec 8) (g : Fin 32 → Word), n - pos < k → pos < 2 ^ 32 → Out M0 M s 228 →
      Slots gtCs F Mp M → memLoad32 M F = p → memLoad32 M (F + 4) = BitVec.ofNat 32 n →
      memLoad32 M (F + 8) = BitVec.ofNat 32 pos → g sp = F → g 18 = out → g 21 = BitVec.ofNat 32 kl →
      g 22 = kq → (∀ x, x ∉ gtE → g x = g0 x) →
      WP jsonGetCode base (RPost (g0 ra) (fun M' => GetResF M0 M' out s 228
        (getRes p (getOut (getFrom (memBytes M0 p n) (memBytes M0 kq kl) k pos)))) g0) M 0x44 g := by
  have halF : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hal (k := 164) (by decide)
  have hFc : F + 0xC = s + BitVec.ofNat 32 176 := by rw [← hF, BitVec.add_assoc]; rfl
  have hF8 : F + 8 = s + BitVec.ofNat 32 172 := by rw [← hF, BitVec.add_assoc]; rfl
  have hFm : F + 0xFFFFFFFC = s + BitVec.ofNat 32 160 := by rw [← hF, BitVec.add_assoc]; rfl
  have hsoF : Sep out 12 F 64 := by rw [← hF]; exact hso.subR (by decide)
  have hlen : (memBytes M0 p n).length = n := memBytes_length M0 p n
  intro k
  induction k with
  | zero => intro pos _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
  intro pos M g hk hpos hO hS hmp hmn hmq hsp h18 h21 h22 hfr
  refine WP.zero fun hz => ?_
  have hc1 : GetCode M base := hcode.out hO hgs
  have hd : memBytes M p n = memBytes M0 p n := hO.bytes hSp
  refine WP.aluImm gt_at_44 ?_; wn
  refine WP.alu gt_at_46 ?_; wn
  have r1 : RiSep s 164 (base + 0xFFFFF438 + 0x1DE) := by
    have := hgs.ri.sub (c := 0) (l := 164) (by decide); rw [add_ofNat_zero] at this; rw [gt_ad_ri]; exact this
  have r2 : Sep (F + 0xC) 20 s 164 := by rw [← hF]; exact (gt_below (c := 12) (w := 20) rfl (by decide)).symm
  have r3 : Sep F 12 s 164 := by
    have := (gt_below (c := 0) (w := 12) hF (by decide)).symm; rwa [add_ofNat_zero] at this
  have r4 : Sep (F + 0xC) 20 F 12 := by
    have := sep_offsets F (c := 12) (n := 20) (d := 0) (k := 12) (Or.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine WP.callNextMember (tb := base + 0xFFFFF438) (out := F + 0xC) (c := F) (s := s) (p := p) (n := n)
    (pos := pos) gt_at_48 gt_at_4c (by simp only [BitVec.add_assoc]; rfl) (even_at base hb _ (by decide))
    (by decide) hc1.nm (by rw [gt_ad_ri]; exact hc1.ri) (by rw [gt_ad_ke]; exact hc1.ke)
    (by (try rsimp); rw [hsp, ev_add]) (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hsp)
    (by (try rsimp); rw [hsp, hF]) hal (aligned_add halF (k := 12) (by decide)) halF hmp hmn hmq hn hpos hp0
    (by omega) r1 (by rw [gt_ad_ke]; exact sep_low hgs.ke (by decide)) (sep_low hgs.nm (by decide))
    (sep_low hSp (by decide)) r2 r3 r4
    (gtSepF (c := 12) (w := 20) hF hgs.nm (by decide)) (gtSepF0 hF hgs.nm)
    (sep_low hgs.get (by decide)) (gtSepF (c := 12) (w := 20) hF hgs.get (by decide)) (gtSepF0 hF hgs.get)
    fun m2 hR => ?_
  rw [hd] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hMR⟩ := hR
  have hO2 : Out M0 M2 s 228 := by
    refine hO.trans ((hOa.mono (by decide)).trans fun x hx => hMR.out ?_ ?_)
    · rw [hFc]; exact sep_in hx (by decide)
    · rw [hF8]; exact sep_in hx (by decide)
  have hcs1 : ∀ c, c ∈ gtCs → (c + 4 ≤ 12 ∨ 12 + 20 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hcs2 : ∀ c, c ∈ gtCs → (c + 4 ≤ 8 ∨ 8 + 4 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hcs3 : ∀ c, c ∈ gtCs → 164 + c + 4 ≤ 2 ^ 32 := by decide
  have hS2 : Slots gtCs F Mp M2 :=
    hMR.slots (hS.out hOa fun c hc => gt_below hF (hcs3 c hc))
      (slots_sep F hcs1 (by decide)) (slots_sep F hcs2 (by decide))
  have hmp2 : memLoad32 M2 F = p := by
    have := hMR.keep (c := 0) (by decide); rw [add_ofNat_zero] at this
    have h2 := hOa.load32 (a := F) (by have := gt_below (c := 0) (w := 4) hF (by decide); rwa [add_ofNat_zero] at this)
    rw [this, h2, hmp]
  have hmn2 : memLoad32 M2 (F + 4) = BitVec.ofNat 32 n := by
    rw [show F + 4 = F + BitVec.ofNat 32 4 from rfl, hMR.keep (by decide),
      hOa.load32 (gt_below (c := 4) (w := 4) hF (by decide))]; exact hmn
  have hc2 : GetCode M2 base := hcode.out hO2 hgs
  refine WP.zero fun hz2 => ?_
  refine WP.lbu gt_at_50 ?_; wn
  generalize hnm : nextMember (memBytes M0 p n) pos = r at hMR
  rcases r with _ | _ | ⟨kp, kl', vp, vl, a⟩
  · obtain ⟨-, t1, t2⟩ := hMR
    have t2' : M2 (F + 0xD) = 0x20 := by
      rw [show F + 0xD = F + 0xC + 1 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch gt_at_54 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lbu gt_at_7e ?_; wn
    refine WP.sb gt_at_82 (by (try rsimp); rw [h18]; exact hsc.sub (c := 1) (by decide)) ?_; wn
    (try rsimp); rw [h18, hsp, t2', ri_ze]
    refine WP.aluImm gt_at_86 ?_; wn
    refine WP.jal gt_at_88 (by decide) ?_; wn
    have hS3 : Slots gtCs F Mp (memStore8 M2 (out + 1) 0x20) :=
      hS2.out (out_store8 _ _ _) (slots_sep_out (hsoF.sub (c := 1) (l := 1) (by decide)) (by decide))
    refine gt_8e (by (try rsimp); exact hsp) (by (try rsimp); exact h18) hS3 hv hsp0 hret halF hz0 (by keepz hz0)
      (sep_low hsoF (by decide)) (sep_low hsc (by decide)) ?_
    (try rsimp); (try simp only [ev0, ev_mv hz2])
    simp only [getFrom, hnm, getOut]
    exact ⟨M2, hO2, get_err M2 out 0x20⟩
  · obtain ⟨-, t1, t2⟩ := hMR
    have t2' : memLoad32 M2 (F + 0x10) = 0 := by
      rw [show F + 0x10 = F + 0xC + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch gt_at_54 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw gt_at_56 (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 0x10) (by decide)) ?_; wn
    refine WP.branch gt_at_58 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hsp, t2'] at eb; exact absurd eb (by decide)
    refine WP.sw gt_at_8a (by (try rsimp); rw [h18]; exact aligned_add halo (k := 4) (by decide))
      (by (try rsimp); rw [h18]; exact hsc.sub (c := 4) (by decide)) ?_; wn
    have hS3 : Slots gtCs F Mp (memStore32 M2 (out + 4) 0) :=
      hS2.out (out_store32 _ _ _) (slots_sep_out (hsoF.sub (c := 4) (l := 4) (by decide)) (by decide))
    (try rsimp); (try simp only [ev0, ev_mv hz2]); rw [h18]
    refine gt_8e (by (try rsimp); exact hsp) (by (try rsimp); exact h18) hS3 hv hsp0 hret halF hz0 (by keepz hz0)
      (sep_low hsoF (by decide)) (sep_low hsc (by decide)) ?_
    (try rsimp); rw [hsp, t2']
    simp only [getFrom, hnm, getOut]
    exact ⟨M2, hO2, get_none M2 out⟩
  obtain ⟨-, t1, tkq, tkl, tvq, tvl, ta⟩ := hMR
  obtain ⟨-, hpa, hkk, han⟩ := nextMember_lt hnm
  rw [hlen] at hkk han
  have tkq' : memLoad32 M2 (F + 0x10) = p + BitVec.ofNat 32 kp := by
    rw [show F + 0x10 = F + 0xC + 4 by rw [BitVec.add_assoc]; rfl]; exact tkq
  have tkl' : memLoad32 M2 (F + 0x14) = BitVec.ofNat 32 kl' := by
    rw [show F + 0x14 = F + 0xC + 8 by rw [BitVec.add_assoc]; rfl]; exact tkl
  have tvq' : memLoad32 M2 (F + 0x18) = p + BitVec.ofNat 32 vp := by
    rw [show F + 0x18 = F + 0xC + 12 by rw [BitVec.add_assoc]; rfl]; exact tvq
  have tvl' : memLoad32 M2 (F + 0x1C) = BitVec.ofNat 32 vl := by
    rw [show F + 0x1C = F + 0xC + 16 by rw [BitVec.add_assoc]; rfl]; exact tvl
  refine WP.branch gt_at_54 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hsp, t1] at eb; exact absurd eb (by decide)
  refine WP.lw gt_at_56 (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 0x10) (by decide)) ?_; wn
  refine WP.branch gt_at_58 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb)
    rw [hsp, tkq', nx_q0 hp0 (n := n + 1) (by omega) (by omega)] at eb; exact absurd eb (by decide)
  refine WP.lw gt_at_5a (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 0x14) (by decide)) ?_; wn
  refine WP.lw gt_at_5c (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 0x18) (by decide)) ?_; wn
  refine WP.lw gt_at_5e (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 0x1C) (by decide)) ?_; wn
  refine WP.alu gt_at_60 ?_; wn
  refine WP.alu gt_at_62 ?_; wn
  have e1 : Sep (s + BitVec.ofNat 32 160) 4 (base + 0xFFFFFFEA + 0xFFFFEBAA) equalSameLengthCode.length := by
    rw [gt_ad_es]; exact hgs.ri.es.sub (by decide)
  have e2 : Sep (s + BitVec.ofNat 32 160) 4 (base + 0xFFFFFFEA + 0xBF68) memcmpCode.length := by
    rw [gt_ad_mm]; exact hgs.ri.mc.sub (by decide)
  have e3 : Sep (s + BitVec.ofNat 32 160) 4 (p + BitVec.ofNat 32 kp) kl' := (hSp.subR hkk).sub (by decide)
  refine WP.callSliceEq (tb := base + 0xFFFFFFEA) (p := p + BitVec.ofNat 32 kp) (q := kq) (pl := kl') (ql := kl)
    gt_at_64 gt_at_68 (by simp only [BitVec.add_assoc]; rfl) (even_at base hb _ (by decide)) (by decide)
    hc2.eq (by rw [gt_ad_es]; exact hc2.ri.es) (by rw [gt_ad_mm]; exact hc2.ri.mc)
    (by (try rsimp); rw [hsp, tkq']) (by (try rsimp); rw [hsp, tkl'])
    (by (try rsimp); (try simp only [ev0, ev_mv hz2]); exact h22)
    (by (try rsimp); (try simp only [ev0, ev_mv hz2]); exact h21) (by omega) hkl
    (by (try rsimp); rw [hsp]; exact halF) (by (try rsimp); rw [hsp, hFm]; exact e1)
    (by (try rsimp); rw [hsp, hFm]; exact e2) (by (try rsimp); rw [hsp, hFm]; exact e3)
    (by (try rsimp); rw [hsp, hFm]; exact hSk.sub (by decide))
    (by (try rsimp); rw [hsp, hFm]; exact hgs.get.sub (by decide)) fun m3 ha0 hO3 => ?_
  refine WP.zero fun hz3 => ?_
  have hO3' : Out M2 m3.mem (s + BitVec.ofNat 32 160) 4 := by
    (try rsimp at hO3); rw [hsp, hFm] at hO3; exact hO3
  have hkey : memBytes M2 (p + BitVec.ofNat 32 kp) kl' = ((memBytes M0 p n).drop kp).take kl' := by
    rw [memBytes_slice hkk]; exact hO2.bytes (hSp.subR hkk)
  rw [hkey, hO2.bytes hSk] at ha0
  generalize m3.mem = M3 at hO3'
  have hO3 : Out M0 M3 s 228 := hO2.trans (hO3'.widen (by decide))
  have hS3 : Slots gtCs F Mp M3 := hS2.out hO3' fun c hc => by
    rw [← hF, add_ofNat_assoc]
    exact sep_offsets s (Or.inl (by omega)) (by decide) (by have := hcs3 c hc; omega)
  have q0 : Sep (s + BitVec.ofNat 32 160) 4 F 4 := by
    rw [← hF]
    exact sep_offsets s (c := 160) (n := 4) (d := 164) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
  have q4 : Sep (s + BitVec.ofNat 32 160) 4 (F + 4) 4 := by
    rw [show F + 4 = s + BitVec.ofNat 32 168 by rw [← hF, BitVec.add_assoc]; rfl]
    exact sep_offsets s (c := 160) (n := 4) (d := 168) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
  have q8 : Sep (s + BitVec.ofNat 32 160) 4 (F + 8) 4 := by
    rw [hF8]
    exact sep_offsets s (c := 160) (n := 4) (d := 172) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
  refine WP.branch gt_at_6c (fun eb => ?_) (fun eb => ?_) <;> wn
  · (try rsimp at eb); rw [ha0] at eb
    have hne : ¬ ((memBytes M0 p n).drop kp).take kl' = memBytes M0 kq kl := fun h => by
      rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at eb; exact absurd eb (by decide)
    simp only [getFrom, hnm]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
    exact ih a M3 _ (by omega) (by omega) hO3 hS3 ((hO3'.load32 q0).trans hmp2) ((hO3'.load32 q4).trans hmn2)
      ((hO3'.load32 q8).trans ta) (by (try rsimp); exact hsp) (by (try rsimp); exact h18)
      (by (try rsimp); exact h21) (by (try rsimp); exact h22) (by keepz hz0)
  (try rsimp at eb); rw [ha0] at eb
  have heq : ((memBytes M0 p n).drop kp).take kl' = memBytes M0 kq kl := by
    refine Decidable.byContradiction fun h => ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false h)] at eb; exact absurd eb (by decide)
  refine WP.aluImm gt_at_6e ?_; wn
  refine WP.alu gt_at_70 ?_; wn
  refine WP.sw gt_at_72 
    (by (try rsimp); (try simp only [ev0, ev_mv hz3]); rw [h18]; exact aligned_add halo (k := 4) (by decide))
    (by (try rsimp); (try simp only [ev0, ev_mv hz3]); rw [h18]; exact hsc.sub (c := 4) (by decide)) ?_; wn
  refine WP.sw gt_at_74 
    (by (try rsimp); (try simp only [ev0, ev_mv hz3]); rw [h18]; exact aligned_add halo (k := 8) (by decide))
    (by (try rsimp); (try simp only [ev0, ev_mv hz3]); rw [h18]; exact hsc.sub (c := 8) (by decide)) ?_; wn
  (try rsimp); (try simp only [ev0, ev_mv hz3]); rw [h18, hsp, tvq', tvl']
  refine WP.jal gt_at_76 (by decide) ?_; wn
  have hS4 : Slots gtCs F Mp (memStore32 (memStore32 M3 (out + 4) (p + BitVec.ofNat 32 vp)) (out + 8)
      (BitVec.ofNat 32 vl)) :=
    (hS3.out (out_store32 _ _ _) (slots_sep_out (hsoF.sub (c := 4) (l := 4) (by decide)) (by decide))).out
      (out_store32 _ _ _) (slots_sep_out (hsoF.sub (c := 8) (l := 4) (by decide)) (by decide))
  refine gt_8e (by (try rsimp); exact hsp) (by (try rsimp); exact h18) hS4 hv hsp0 hret halF hz0 (by keepz hz0)
    (sep_low hsoF (by decide)) (sep_low hsc (by decide)) ?_
  (try rsimp); (try simp only [ev0, ev_mv hz3])
  simp only [getFrom, hnm]
  rw [ite_eq_left_of_eq_true _ _ (eq_true heq)]
  exact ⟨M3, hO3, get_some M3 out (p + BitVec.ofNat 32 vp) vl⟩
end

theorem objGet_none {p : Word} {d key : Bytes} (h : curOpen 123 p d = none) : objGet d key = .error 0x21 := by
  unfold objGet
  refine ite_eq_left_of_eq_true _ _ (eq_true ?_)
  unfold curOpen at h
  split at h
  · exact Or.inl ‹_›
  · split at h
    · exact Or.inr ‹_›
    · nomatch h

theorem objGet_some {p q : Word} {d key : Bytes} {l k : Nat} (h : curOpen 123 p d = some (q, l, k)) :
    q = p ∧ l = d.length ∧ k = skipWs d 1 ∧
      objGet d key = getOut (getFrom d key (d.length + 1) (skipWs d 1)) := by
  unfold curOpen at h
  split at h
  · nomatch h
  · rename_i h1
    split at h
    · nomatch h
    · rename_i h2
      cases h
      refine ⟨rfl, rfl, rfl, ?_⟩
      unfold objGet
      exact ite_eq_right_of_eq_false _ _ (eq_false fun h' => h'.elim h1 h2)

theorem copyBytes_at {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  unfold copyBytes
  rw [add_sub_toNat dst (by omega), ite_eq_left hi, BitVec.add_comm dst, BitVec.add_sub_cancel]

theorem toNat_add_lt {s : Word} {c : Nat} (h : s.toNat + c < 2 ^ 32) :
    (s + BitVec.ofNat 32 c).toNat = s.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega), Nat.mod_eq_of_lt h]

section
variable {M0 : Word → BitVec 8} {base out s p kq : Word} {f : Fin 32 → Word} {n kl : Nat}

theorem gt_wp (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n) (h3 : f a3 = kq)
    (h4 : f a4 = BitVec.ofNat 32 kl) (hsp : f sp = s + BitVec.ofNat 32 228) (hret : f ra &&& ~~~1 = f ra)
    (hb : base.toNat % 2 = 0) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hsw : s.toNat + 228 < 2 ^ 32)
    (hn : n < 2 ^ 32) (hkl : kl < 2 ^ 32) (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32)
    (hcode : GetCode M0 base) (hgs : GetSep s 228 base) (hSp : Sep s 228 p n) (hSk : Sep s 228 kq kl)
    (hso : Sep out 12 s 228) (hsc : Sep out 12 base jsonGetCode.length) :
    WP jsonGetCode base (RPost (f ra) (fun M' => GetResF M0 M' out s 228
      (getRes p (objGet (memBytes M0 p n) (memBytes M0 kq kl)))) f) M0 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFC0 = s + 164 := by rw [hsp, ev_add, BitVec.add_assoc]; rfl
  refine WP.aluImm gt_at_0 ?_; wn
  rw [esp]
  generalize hF : s + 164 = F
  have hF' : s + BitVec.ofNat 32 164 = F := hF
  have halF : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hal (k := 164) (by decide)
  have hsp0 : f sp = F + BitVec.ofNat 32 0x40 := by rw [hsp, ← hF, BitVec.add_assoc]; rfl
  refine WP.sw gt_at_2 (by rsimp; exact aligned_add halF (k := 0x3C) (by decide))
    (by rsimp; exact gtSepF hF' hgs.get (by decide)) ?_; wn
  refine WP.sw gt_at_4 (by rsimp; exact aligned_add halF (k := 0x38) (by decide))
    (by rsimp; exact gtSepF hF' hgs.get (by decide)) ?_; wn
  refine WP.sw gt_at_6 (by rsimp; exact aligned_add halF (k := 0x34) (by decide))
    (by rsimp; exact gtSepF hF' hgs.get (by decide)) ?_; wn
  refine WP.sw gt_at_8 (by rsimp; exact aligned_add halF (k := 0x30) (by decide))
    (by rsimp; exact gtSepF hF' hgs.get (by decide)) ?_; wn
  refine WP.sw gt_at_a (by rsimp; exact aligned_add halF (k := 0x2C) (by decide))
    (by rsimp; exact gtSepF hF' hgs.get (by decide)) ?_; wn
  refine WP.sw gt_at_c (by rsimp; exact aligned_add halF (k := 0x28) (by decide))
    (by rsimp; exact gtSepF hF' hgs.get (by decide)) ?_; wn
  refine WP.sw gt_at_e (by rsimp; exact aligned_add halF (k := 0x24) (by decide))
    (by rsimp; exact gtSepF hF' hgs.get (by decide)) ?_; wn
  refine WP.sw gt_at_10 (by rsimp; exact aligned_add halF (k := 0x20) (by decide))
    (by rsimp; exact gtSepF hF' hgs.get (by decide)) ?_; wn
  change WP jsonGetCode base _ (gtM1 M0 F f) 0x12 _
  obtain ⟨hO1, hv⟩ := gt_pro M0 F f
  have hO1' : Out M0 (gtM1 M0 F f) s 228 := Out.upK hF' hO1 (by decide)
  have hS : Slots gtCs F (gtM1 M0 F f) (gtM1 M0 F f) := Slots.refl _ _ _
  have hc1 : GetCode (gtM1 M0 F f) base := hcode.out hO1' hgs
  have hd1 : memBytes (gtM1 M0 F f) p n = memBytes M0 p n := hO1'.bytes hSp
  generalize gtM1 M0 F f = M at hO1' hS hc1 hd1 hv
  have hFc : F + 0xC = s + BitVec.ofNat 32 176 := by rw [← hF', BitVec.add_assoc]; rfl
  have hcs3 : ∀ c, c ∈ gtCs → 164 + c + 4 ≤ 2 ^ 32 := by decide
  have hlen : (memBytes M0 p n).length = n := memBytes_length M0 p n
  refine WP.alu gt_at_12 ?_; wn
  refine WP.alu gt_at_14 ?_; wn
  refine WP.alu gt_at_16 ?_; wn
  refine WP.aluImm gt_at_18 ?_; wn
  have m1 : Sep (F + 0xC) 12 (s + BitVec.ofNat 32 148) 16 := by
    rw [hFc]; exact sep_offsets s (c := 176) (n := 12) (d := 148) (k := 16) (Or.inr (by decide)) (by decide) (by decide)
  refine WP.callMembers (tb := base + 0xA6) (out := F + 0xC) (s := s + BitVec.ofNat 32 148) (p := p) (n := n)
    gt_at_1a gt_at_1e (by simp only [BitVec.add_assoc]; rfl) (even_at base hb _ (by decide)) (by decide)
    hc1.me (by rw [gt_ad_sw]; exact hc1.ri.sw) (by (try rsimp); (try rw [ev_add]))
    (by (try rsimp); exact h1) (by (try rsimp); exact h2) (by (try rsimp); rw [← hF', BitVec.add_assoc]; rfl)
    hn (aligned_add hal (k := 148) (by decide)) (aligned_add halF (k := 12) (by decide))
    (hgs.me.sub (by decide)) (by rw [gt_ad_sw]; exact hgs.ri.sw.sub (by decide)) (hSp.sub (by decide)) m1
    (gtSepF (c := 12) (w := 12) hF' hgs.me (by decide)) (hgs.get.sub (by decide))
    (gtSepF (c := 12) (w := 12) hF' hgs.get (by decide)) fun m2 hR => ?_
  rw [hd1] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hCR⟩ := hR
  have hO2 : Out M0 M2 s 228 := by
    have := hCR.out; rw [hFc] at this
    exact hO1'.trans ((hOa.widen (by decide)).trans (this.widen (by decide)))
  have hcs1 : ∀ c, c ∈ gtCs → (c + 4 ≤ 12 ∨ 12 + 12 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hS2 : Slots gtCs F M M2 := by
    refine (hS.out hOa fun c hc => ?_).out hCR.out (slots_sep F hcs1 (by decide))
    rw [← hF', add_ofNat_assoc]
    exact sep_offsets s (Or.inl (by omega)) (by decide) (by have := hcs3 c hc; omega)
  have hc2 : GetCode M2 base := hcode.out hO2 hgs
  refine WP.zero fun hz2 => ?_
  refine WP.lw gt_at_22 (by (try rsimp); exact aligned_add halF (k := 0xC) (by decide)) ?_; wn
  refine WP.lbu gt_at_24 ?_; wn
  rcases hco : curOpen 123 p (memBytes M0 p n) with _ | ⟨q, l, kk⟩ <;> rw [hco] at hCR
  · obtain ⟨-, t1, t2⟩ := hCR
    have t2' : M2 (F + 0x10) = 0x21 := by
      rw [show F + 0x10 = F + 0xC + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch gt_at_28 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [t1] at eb; exact absurd eb (by decide)
    refine WP.sb gt_at_78 (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h0]; exact hsc.sub (c := 1) (by decide)) ?_
    wn
    (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h0, t2', ri_ze]
    refine WP.jal gt_at_7c (by decide) ?_; wn
    refine WP.aluImm gt_at_86 ?_; wn
    refine WP.jal gt_at_88 (by decide) ?_; wn
    have hsoF : Sep out 12 F 64 := by rw [← hF']; exact hso.subR (by decide)
    have hS3 : Slots gtCs F M (memStore8 M2 (out + 1) 0x21) :=
      hS2.out (out_store8 _ _ _) (slots_sep_out (hsoF.sub (c := 1) (l := 1) (by decide)) (by decide))
    refine gt_8e (by rsimp) (by (try rsimp); (try simp only [ev0, ev_mv hz]); try exact h0) hS3 hv hsp0 hret halF hz
      (by keepz hz) (sep_low hsoF (by decide)) (sep_low hsc (by decide)) ?_
    (try rsimp); (try simp only [ev0, ev_mv hz2])
    rw [objGet_none hco]
    exact ⟨M2, hO2, get_err M2 out 0x21⟩
  obtain ⟨hq, hl, hk, hobj⟩ := objGet_some (key := memBytes M0 kq kl) hco
  rw [hlen] at hl hobj
  rw [hq, hl, hk] at hCR
  obtain ⟨-, t1, t2, t3⟩ := hCR
  have t2' : memLoad32 M2 (F + 0x10) = BitVec.ofNat 32 n := by
    rw [show F + 0x10 = F + 0xC + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
  have t3' : memLoad32 M2 (F + 0x14) = BitVec.ofNat 32 (skipWs (memBytes M0 p n) 1) := by
    rw [show F + 0x14 = F + 0xC + 8 by rw [BitVec.add_assoc]; rfl]; exact t3
  have hq0 := nx_q0 hp0 (n := 1) (pos := 0) (by omega) (by omega)
  rw [add_ofNat_zero] at hq0
  refine WP.branch gt_at_28 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [t1, hq0] at eb; exact absurd eb (by decide)
  refine WP.aluImm gt_at_2c ?_; wn
  refine WP.aluImm gt_at_30 ?_; wn
  refine WP.aluImm gt_at_34 ?_; wn
  have hFt : ∀ c : Nat, 164 + c ≤ 228 → (F + BitVec.ofNat 32 c).toNat = s.toNat + 164 + c := fun c hc => by
    rw [← hF', add_ofNat_assoc, toNat_add_lt (by omega)]; omega
  have E : McEnv M2 (base + 0xBFDA + 8) (F + 5) (F + 0x11) (s + BitVec.ofNat 32 148) 7 := by
    refine ⟨by rw [gt_ad_mc]; exact hc2.mc, by rw [gt_ad_mc]; exact gtSepF hF' hgs.mc (by decide),
      by rw [gt_ad_mc]; exact hgs.mc.sub (by decide), ?_, ?_, ?_, aligned_add hal (k := 148) (by decide), ?_, ?_, ?_⟩
    · show Sep (F + BitVec.ofNat 32 5) 7 _ 16
      rw [← hF', add_ofNat_assoc]
      exact sep_offsets s (c := 169) (n := 7) (d := 148) (k := 16) (Or.inr (by decide)) (by decide) (by decide)
    · show Sep (F + BitVec.ofNat 32 17) 7 _ 16
      rw [← hF', add_ofNat_assoc]
      exact sep_offsets s (c := 181) (n := 7) (d := 148) (k := 16) (Or.inr (by decide)) (by decide) (by decide)
    · exact sep_offsets F (c := 5) (n := 7) (d := 17) (k := 7) (Or.inl (by decide)) (by decide) (by decide)
    · rw [toNat_add_lt (by omega)]; omega
    · show (F + BitVec.ofNat 32 5).toNat + 7 < 2 ^ 32
      rw [hFt 5 (by decide)]; omega
    · show (F + BitVec.ofNat 32 17).toNat + 7 < 2 ^ 32
      rw [hFt 17 (by decide)]; omega
  refine WP.callMemcpy (tb := base + 0xBFDA) (dst := F + 5) (src := F + 0x11) (F := s + BitVec.ofNat 32 148)
    (N := 7) gt_at_36 gt_at_3a (by simp only [BitVec.add_assoc]; rfl) (even_at base hb _ (by decide)) (by decide)
    hc2.stub E (by (try rsimp); (try rw [ev_add])) (by (try rsimp); (try rw [ev_add]))
    (by (try rsimp); (try simp only [ev0, ev_mv hz2]); try rfl)
    (by (try rsimp); rw [← hF', BitVec.add_assoc]; rfl) (hgs.get.sub (by decide))
    (gtSepF (c := 5) (w := 7) hF' hgs.get (by decide)) fun m3 hO3 => ?_
  generalize m3.mem = M3 at hO3
  refine WP.sw gt_at_3e (by (try rsimp); rw [add_lit_zero]; exact halF)
    (by (try rsimp); rw [add_lit_zero]; exact sep_low (gtSepF0 hF' hgs.get) (by decide)) ?_; wn
  refine WP.sb gt_at_40 (by (try rsimp); exact gtSepF (c := 4) (w := 1) hF' hgs.get (by decide)) ?_; wn
  (try rsimp); rw [add_lit_zero, t1, ri_ze]
  have oC : Out M2 (copyBytes M2 (F + 5) (F + 0x11) 7) (F + 5) 7 := fun x hx => copyBytes_sep hx.symm (Nat.le_refl _)
  have e5 : s + BitVec.ofNat 32 169 = F + 5 := by rw [← hF', BitVec.add_assoc]; rfl
  have e4 : s + BitVec.ofNat 32 168 = F + 4 := by rw [← hF', BitVec.add_assoc]; rfl
  have hO5 : Out M0 (memStore8 (memStore32 M3 F p) (F + 4) (M2 (F + 0x10))) s 228 :=
    hO2.trans ((Out.upK e5 oC (by decide)).trans ((hO3.widen (by decide)).trans
      ((Out.upK hF' (out_store32 _ _ _) (by decide)).trans (Out.upK e4 (out_store8 _ _ _) (by decide)))))
  have hcs5 : ∀ c, c ∈ gtCs → (c + 4 ≤ 5 ∨ 5 + 7 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hcs0 : ∀ c, c ∈ gtCs → (c + 4 ≤ 0 ∨ 0 + 4 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hcs4 : ∀ c, c ∈ gtCs → (c + 4 ≤ 4 ∨ 4 + 1 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hS5 : Slots gtCs F M (memStore8 (memStore32 M3 F p) (F + 4) (M2 (F + 0x10))) := by
    refine (((hS2.out oC (slots_sep F hcs5 (by decide))).out hO3 fun c hc => ?_).out (out_store32 _ _ _)
      fun c hc => ?_).out (out_store8 _ _ _) (slots_sep F hcs4 (by decide))
    · rw [← hF', add_ofNat_assoc]
      exact sep_offsets s (Or.inl (by omega)) (by decide) (by have := hcs3 c hc; omega)
    · have := slots_sep F hcs0 (by decide) c hc; rwa [add_ofNat_zero] at this
  generalize hM5 : memStore8 (memStore32 M3 F p) (F + 4) (M2 (F + 0x10)) = M5 at hO5 hS5
  have hcp : ∀ c, 5 ≤ c → c < 12 → M5 (F + BitVec.ofNat 32 c) = M2 (F + BitVec.ofNat 32 (c + 12)) := by
    intro c hc1 hc2
    rw [← hM5, memStore8_ne ?_]
    · rw [out_store32 _ _ _ _ ?_, hO3 _ ?_]
      · have := copyBytes_at (M := M2) (dst := F + BitVec.ofNat 32 5) (src := F + BitVec.ofNat 32 17) (N := 7)
          (i := c - 5) (by omega) (by decide)
        rw [add_ofNat_assoc, add_ofNat_assoc, show 5 + (c - 5) = c by omega, show 17 + (c - 5) = c + 12 by omega]
          at this
        exact this
      · rw [← hF', add_ofNat_assoc]
        exact sep_offsets s (c := 164 + c) (n := 1) (d := 148) (k := 16) (Or.inr (by omega)) (by omega) (by decide)
      · have := sep_offsets F (c := c) (n := 1) (d := 0) (k := 4) (Or.inr (by omega)) (by omega) (by decide)
        rwa [add_ofNat_zero] at this
    · have := sep_offsets F (c := c) (n := 1) (d := 4) (k := 1) (Or.inr (by omega)) (by omega) (by decide)
      exact sep_byte0 this (by decide)
  have hm0 : memLoad32 M5 F = p := by
    have h4F : Sep (F + 4) 1 F 4 := by
      have := sep_offsets F (c := 4) (n := 1) (d := 0) (k := 4) (Or.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    rw [← hM5, (out_store8 _ _ _).load32 h4F, memLoad32_store32_same]
  have hm4 : memLoad32 M5 (F + 4) = BitVec.ofNat 32 n := by
    rw [← t2']
    refine memLoad32_shift fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [add_ofNat_zero, add_ofNat_zero, ← hM5, memStore8_same]
    · show M5 (F + BitVec.ofNat 32 4 + BitVec.ofNat 32 j) = M2 (F + BitVec.ofNat 32 16 + BitVec.ofNat 32 j)
      rw [add_ofNat_assoc, add_ofNat_assoc, hcp (4 + j) (by omega) (by omega), show 4 + j + 12 = 16 + j by omega]
  have hm8 : memLoad32 M5 (F + 8) = BitVec.ofNat 32 (skipWs (memBytes M0 p n) 1) := by
    rw [← t3']
    refine memLoad32_shift fun j hj => ?_
    show M5 (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 j) = M2 (F + BitVec.ofNat 32 20 + BitVec.ofNat 32 j)
    rw [add_ofNat_assoc, add_ofNat_assoc, hcp (8 + j) (by omega) (by omega), show 8 + j + 12 = 20 + j by omega]
  have hsk := skipWs_le (memBytes M0 p n) 1
  rw [hobj]
  exact gt_loop M0 hF' hb hal halo hn hkl hp0 hpn hcode hgs hSp hSk hso hsc hv hsp0 hret hz (n + 1) _ M5 _
    (by omega) (by omega) hO5 hS5 hm0 hm4 hm8 (by rsimp)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); try exact h0)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); try exact h4)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); try exact h3) (by keepz hz)
end

/-- `get(key)` on the `n` bytes at `p`, with the key the `kl` bytes at `kq`
and `sp = s + 228`, returns with `out` holding `objGet doc key`, its offsets
moved to addresses by `getRes p`: `Ok(Some(value))` for the first member whose
key equals the key, `Ok(None)` when none does, or the error byte (`0x21` when
the document isn't an object, `0x20` when a member isn't valid JSON). It
changes memory only in the 228 bytes at `s` and the 12 bytes at `out`, and
keeps every register outside `jClob`. The callees are where `GetCode` lists
them. -/
theorem jsonGet_correct (m : Machine) {base retAddr out s p kq : Word} {n kl : Nat}
    (hb : base.toNat % 2 = 0) (hc : GetCode m.mem base) (hpc : m.pc = base) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n) (ha3 : reg m a3 = kq)
    (ha4 : reg m a4 = BitVec.ofNat 32 kl) (hsp : reg m sp = s + BitVec.ofNat 32 228) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hsw : s.toNat + 228 < 2 ^ 32) (hkl : kl < 2 ^ 32) (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n < 2 ^ 32)
    (hgs : GetSep s 228 base) (hSp : Sep s 228 p n) (hSk : Sep s 228 kq kl) (hso : Sep out 12 s 228)
    (hsc : Sep out 12 base jsonGetCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      GetResF m.mem m'.mem out s 228 (getRes p (objGet (memBytes m.mem p n) (memBytes m.mem kq kl))) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (gt_wp ha0 ha1 ha2 ha3 ha4 hsp (by rw [hra]; exact hret) hb hal halo
    hsw (by omega) hkl hp0 hpn hc hgs hSp hSk hso hsc) hb hc.get hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
