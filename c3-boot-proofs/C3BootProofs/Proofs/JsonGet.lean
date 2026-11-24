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

/-- A member starts before the end, ends after its start, and has its key
inside the object. -/
theorem nextMember_lt {d : Bytes} {pos kp kl vp vl a : Nat}
    (h : nextMember d pos = some (some (kp, kl, vp, vl, a))) :
    pos < d.length ∧ pos < a ∧ kp + kl ≤ d.length := by
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
        exact ⟨hlt, by omega, by omega⟩

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

end C3.RV32
