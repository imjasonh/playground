import C3BootProofs.Proofs.TufHex
import C3BootProofs.Proofs.LeafStep

/-!
# `tuf::hex_decode`, as compiled

`hex_decode(text, out)` decodes lowercase hex `text` into the 128-byte
buffer `out`. The compiled function takes `text` as a pointer and length in
`a0` and `a1` and `out` in `a2`, calls `tuf::hex_value` for each digit, and
returns the decoded bytes as a pointer in `a0`, null for `None`, and half of
the text's length in `a1` on every path.

`tufHexDecodeSpec` is `parseHex` of the text when the text has at most 256
bytes, the most that fits in `out`, and `None` otherwise.
-/

namespace C3.RV32

open C3 C3.Image

section
set_option maxRecDepth 20000
theorem thd_at_0 : fetchRel tufHexDecodeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem thd_at_2 : fetchRel tufHexDecodeCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem thd_at_4 : fetchRel tufHexDecodeCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem thd_at_6 : fetchRel tufHexDecodeCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem thd_at_8 : fetchRel tufHexDecodeCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem thd_at_a : fetchRel tufHexDecodeCode 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem thd_at_c : fetchRel tufHexDecodeCode 0xC = some (.store .sw sp (20 : Fin 32) 0x8, 2) := by decide
theorem thd_at_e : fetchRel tufHexDecodeCode 0xE = some (.store .sw sp (21 : Fin 32) 0x4, 2) := by decide
theorem thd_at_10 : fetchRel tufHexDecodeCode 0x10 = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem thd_at_12 : fetchRel tufHexDecodeCode 0x12 = some (.aluImm .and a2 a1 0x1, 4) := by decide
theorem thd_at_16 : fetchRel tufHexDecodeCode 0x16 = some (.aluImm .srl (18 : Fin 32) a1 0x1, 4) := by decide
theorem thd_at_1a : fetchRel tufHexDecodeCode 0x1A = some (.branch .bne a2 x0 0xA, 2) := by decide
theorem thd_at_1c : fetchRel tufHexDecodeCode 0x1C = some (.aluImm .add a2 x0 0x101, 4) := by decide
theorem thd_at_20 : fetchRel tufHexDecodeCode 0x20 = some (.branch .bgeu a2 a1 0x1C, 4) := by decide
theorem thd_at_24 : fetchRel tufHexDecodeCode 0x24 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem thd_at_26 : fetchRel tufHexDecodeCode 0x26 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem thd_at_28 : fetchRel tufHexDecodeCode 0x28 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem thd_at_2a : fetchRel tufHexDecodeCode 0x2A = some (.load .lw ra sp 0x1C, 2) := by decide
theorem thd_at_2c : fetchRel tufHexDecodeCode 0x2C = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem thd_at_2e : fetchRel tufHexDecodeCode 0x2E = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem thd_at_30 : fetchRel tufHexDecodeCode 0x30 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem thd_at_32 : fetchRel tufHexDecodeCode 0x32 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem thd_at_34 : fetchRel tufHexDecodeCode 0x34 = some (.load .lw (20 : Fin 32) sp 0x8, 2) := by decide
theorem thd_at_36 : fetchRel tufHexDecodeCode 0x36 = some (.load .lw (21 : Fin 32) sp 0x4, 2) := by decide
theorem thd_at_38 : fetchRel tufHexDecodeCode 0x38 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem thd_at_3a : fetchRel tufHexDecodeCode 0x3A = some (.jalr x0 ra 0x0, 2) := by decide
theorem thd_at_3c : fetchRel tufHexDecodeCode 0x3C = some (.aluImm .sltu a1 a1 0x102, 4) := by decide
theorem thd_at_40 : fetchRel tufHexDecodeCode 0x40 = some (.alu .sub a1 x0 a1, 4) := by decide
theorem thd_at_44 : fetchRel tufHexDecodeCode 0x44 = some (.alu .and (19 : Fin 32) a1 (20 : Fin 32), 4) := by decide
theorem thd_at_48 : fetchRel tufHexDecodeCode 0x48 = some (.aluImm .add (9 : Fin 32) a0 0x1, 4) := by decide
theorem thd_at_4c : fetchRel tufHexDecodeCode 0x4C = some (.alu .add (21 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem thd_at_4e : fetchRel tufHexDecodeCode 0x4E = some (.branch .beq (18 : Fin 32) x0 0xFFFFFFD8, 4) := by decide
theorem thd_at_52 : fetchRel tufHexDecodeCode 0x52 = some (.load .lbu a0 (9 : Fin 32) 0xFFFFFFFF, 4) := by decide
theorem thd_at_56 : fetchRel tufHexDecodeCode 0x56 = some (.auipc ra 0x0, 4) := by decide
theorem thd_at_5a : fetchRel tufHexDecodeCode 0x5A = some (.jalr ra ra 0x32, 4) := by decide
theorem thd_at_5e : fetchRel tufHexDecodeCode 0x5E = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem thd_at_60 : fetchRel tufHexDecodeCode 0x60 = some (.branch .beq a0 x0 0xFFFFFFC4, 2) := by decide
theorem thd_at_62 : fetchRel tufHexDecodeCode 0x62 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem thd_at_64 : fetchRel tufHexDecodeCode 0x64 = some (.load .lbu a0 (9 : Fin 32) 0x0, 4) := by decide
theorem thd_at_68 : fetchRel tufHexDecodeCode 0x68 = some (.auipc ra 0x0, 4) := by decide
theorem thd_at_6c : fetchRel tufHexDecodeCode 0x6C = some (.jalr ra ra 0x20, 4) := by decide
theorem thd_at_70 : fetchRel tufHexDecodeCode 0x70 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem thd_at_72 : fetchRel tufHexDecodeCode 0x72 = some (.branch .beq a0 x0 0xFFFFFFB2, 2) := by decide
theorem thd_at_74 : fetchRel tufHexDecodeCode 0x74 = some (.aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem thd_at_76 : fetchRel tufHexDecodeCode 0x76 = some (.alu .or a1 a1 (8 : Fin 32), 2) := by decide
theorem thd_at_78 : fetchRel tufHexDecodeCode 0x78 = some (.store .sb (20 : Fin 32) a1 0x0, 4) := by decide
theorem thd_at_7c : fetchRel tufHexDecodeCode 0x7C = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x1, 2) := by decide
theorem thd_at_7e : fetchRel tufHexDecodeCode 0x7E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x2, 2) := by decide
theorem thd_at_80 : fetchRel tufHexDecodeCode 0x80 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem thd_at_82 : fetchRel tufHexDecodeCode 0x82 = some (.branch .beq (21 : Fin 32) x0 0xFFFFFFA4, 4) := by decide
theorem thd_at_86 : fetchRel tufHexDecodeCode 0x86 = some (.jal x0 0xFFFFFFCC, 2) := by decide
end

/-- `tuf::hex_decode` into a 128-byte buffer, on the `len` bytes at `text`. -/
def tufHexDecodeSpec (M : Word → BitVec 8) (text : Word) (len : Nat) : Option (List Nat) :=
  if len ≤ 256 then parseHex (memBytes M text len) else none

theorem thd_odd : ∀ (n : Nat) (l : List Nat), l.length = 2 * n + 1 → parseHex l = none
  | _, [], h => absurd h (by rw [List.length_nil]; omega)
  | 0, [_], _ => rfl
  | _ + 1, [_], h => absurd h (by rw [List.length_singleton]; omega)
  | 0, _ :: _ :: _, h => absurd h (by rw [List.length_cons, List.length_cons]; omega)
  | n + 1, a :: b :: rest, h => by
    have hr := thd_odd n rest (by rw [List.length_cons, List.length_cons] at h; omega)
    simp only [parseHex]
    rw [hr]
    generalize hexDigit a = x; generalize hexDigit b = y
    cases x <;> cases y <;> rfl

theorem thd_cons (x y : Nat) (rest : List Nat) : parseHex (x :: y :: rest) =
    (hexDigit x).bind fun h => (hexDigit y).bind fun l => (parseHex rest).map ((16 * h + l) :: ·) := by
  simp only [parseHex]
  generalize hexDigit x = a; generalize hexDigit y = b; generalize parseHex rest = c
  cases a <;> cases b <;> cases c <;> rfl

theorem thd_stepAt (M : Word → BitVec 8) (text : Word) (k d : Nat) :
    parseHex (memBytes M (text + BitVec.ofNat 32 (2 * k)) (2 * (d + 1))) =
      (hexDigit (M (text + BitVec.ofNat 32 (2 * k))).toNat).bind fun h =>
        (hexDigit (M (text + BitVec.ofNat 32 (2 * k + 1))).toNat).bind fun l =>
          (parseHex (memBytes M (text + BitVec.ofNat 32 (2 * (k + 1))) (2 * d))).map ((16 * h + l) :: ·) := by
  rw [show 2 * (d + 1) = 2 * d + 1 + 1 by omega, memBytes_succ, memBytes_succ, thd_cons,
    show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, add_ofNat_assoc,
    show 2 * k + 1 + 1 = 2 * (k + 1) by omega]

theorem thd_map_snoc (X : Option (List Nat)) (bsk : List Nat) (v : Nat) :
    (X.map (v :: ·)).map (bsk ++ ·) = X.map ((bsk ++ [v]) ++ ·) := by
  cases X with
  | none => rfl
  | some l => exact congrArg some (List.append_assoc bsk [v] l).symm

theorem thd_map_nil (X : Option (List Nat)) : X.map ([] ++ ·) = X := by
  cases X <;> rfl

theorem thd_snoc (M : Word → BitVec 8) (q : Word) (j : Nat) :
    memBytes M q (j + 1) = memBytes M q j ++ [(M (q + BitVec.ofNat 32 j)).toNat] := by
  rw [memBytes_split, memBytes_succ, memBytes_zero]

theorem thd_byte : ∀ h l : Fin 16,
    ((aluEval .or (BitVec.ofNat 32 l.val) (aluEval .sll (BitVec.ofNat 32 h.val) 4)).extractLsb' 0 8).toNat =
      16 * h.val + l.val := by decide

theorem thd_digit {c d : Nat} (h : hexDigit c = some d) : d < 16 := by
  unfold hexDigit at h
  by_cases h1 : (48 ≤ c && c ≤ 57) = true
  · rw [if_pos h1] at h
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1
    obtain ⟨-, h1⟩ := h1
    have := Option.some.inj h; omega
  · rw [if_neg h1] at h
    by_cases h2 : (97 ≤ c && c ≤ 102) = true
    · rw [if_pos h2] at h
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h2
      obtain ⟨-, h2⟩ := h2
      have := Option.some.inj h; omega
    · rw [if_neg h2] at h; cases h

theorem thd_zext : ∀ b : BitVec 8, b.zeroExtend 32 = BitVec.ofNat 32 b.toNat := by decide

theorem thd_and1 {len : Nat} (h : len < 2 ^ 32) :
    aluEval .and (BitVec.ofNat 32 len) 1 = BitVec.ofNat 32 (len % 2) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 len &&& 1).toNat = _
  rw [BitVec.toNat_and, ls_ofNat_toNat_lt h, show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod,
    ls_ofNat_toNat_lt (by omega)]

theorem thd_srl1 {len : Nat} (h : len < 2 ^ 32) :
    aluEval .srl (BitVec.ofNat 32 len) 1 = BitVec.ofNat 32 (len / 2) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 len >>> ((1 : Word).toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, ls_ofNat_toNat_lt h, show (1 : Word).toNat % 32 = 1 from rfl,
    Nat.shiftRight_eq_div_pow, ls_ofNat_toNat_lt (by omega)]

theorem thd_dec' {j : Nat} (h0 : 0 < j) (h : j < 2 ^ 32) :
    BitVec.ofNat 32 j + 0xFFFFFFFF = BitVec.ofNat 32 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, ls_ofNat_toNat_lt h, ls_ofNat_toNat_lt (by omega),
    show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
  omega

theorem thd_flag (b : Bool) : aluEval .and (if b = true then (1 : Word) else 0) 1 = if b = true then 1 else 0 := by
  cases b <;> rfl

/-- The registers the decoder's loop leaves alone: all but `ra`, `s0`, and
`a0` through `a5`. -/
def thdJ (q : Fin 32) : Bool := !(q.val == 1 || q.val == 8 || (10 ≤ q.val && q.val ≤ 15))

/-- `thdJ` without the loop's cursors `s1`, `s4`, and `s5`. -/
def thdL (q : Fin 32) : Bool := thdJ q && !(q.val == 9 || q.val == 20 || q.val == 21)

/-- The registers `tuf::hex_decode` never writes. -/
def thdK (q : Fin 32) : Bool := thdL q && !(q.val == 2 || q.val == 18 || q.val == 19)

/-- The registers `tuf::hex_decode` saves and restores. -/
def thdS (q : Fin 32) : Bool := q.val == 1 || q.val == 2 || q.val == 8 || q.val == 9 || (18 ≤ q.val && q.val ≤ 21)

theorem thdJ_ne : ∀ q : Fin 32, thdJ q = true →
    q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ ra := by decide

theorem thdL_J : ∀ q : Fin 32, thdL q = true → thdJ q = true := by decide

theorem thdK_L : ∀ q : Fin 32, thdK q = true → thdL q = true := by decide

theorem thdS_cases : ∀ q : Fin 32, thdS q = true →
    q = ra ∨ q = sp ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 := by decide

theorem thd_cover : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 →
    thdK q = true ∨ thdS q = true := by decide

/-- What `tufHexDecode_correct` concludes from `n`, for a result `r` of
`np` bytes: a run to `retAddr` that returns `out` or null, frames memory
outside `out` to `M7`, and keeps or restores every register but `a0`
through `a5`. -/
def ThdPost (m : Machine) (M7 : Word → BitVec 8) (retAddr out : Word) (np : Nat) (r : Option (List Nat))
    (n : Machine) : Prop :=
  ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ reg n' a0 = (if r.isSome then out else 0) ∧
    reg n' a1 = BitVec.ofNat 32 np ∧ (∀ bs, r = some bs → bs.length = np ∧ memBytes n'.mem out np = bs) ∧
    (∀ q, thdK q = true → reg n' q = reg m q) ∧ (∀ q, thdS q = true → reg n' q = reg m q) ∧
    ∀ x, Sep out 128 x 1 → n'.mem x = M7 x

theorem ThdPost.pre {m n n2 : Machine} {M7 : Word → BitVec 8} {retAddr out : Word} {np : Nat}
    {r : Option (List Nat)} (h : ThdPost m M7 retAddr out np r n2) (c : Steps n n2) :
    ThdPost m M7 retAddr out np r n := by
  obtain ⟨n', c', rest⟩ := h
  exact ⟨n', c.trans c', rest⟩

theorem thd_ne0 {j : Nat} (h0 : 0 < j) (h : j < 2 ^ 32) : BitVec.ofNat 32 j ≠ 0 := fun e => by
  have := congrArg BitVec.toNat e
  rw [ls_ofNat_toNat_lt h] at this
  change j = 0 at this
  omega

theorem thd_st8_ne {M : Word → BitVec 8} {a x : Word} {v : BitVec 8} (h : x ≠ a) : memStore8 M a v x = M x :=
  if_neg h

theorem thd_st8_eq (M : Word → BitVec 8) (a : Word) (v : BitVec 8) : memStore8 M a v a = v := if_pos rfl

set_option maxHeartbeats 8000000 in
/-- **The compiled `tuf::hex_decode`**: called with `text` of `len` bytes
and a 128-byte buffer `out`, it returns `out` in `a0` when
`tufHexDecodeSpec` decodes the text, with the decoded bytes in `out`, and 0
otherwise. `a1` holds `len / 2` either way. It writes only `a0` through
`a5`, the 32 bytes below `sp`, and `out`. -/
theorem tufHexDecode_correct (m : Machine) {base retAddr text out : Word} {len : Nat}
    (hc : CodeIn m.mem base tufHexDecodeCode) (hv : CodeIn m.mem (base + 0x88) tufHexValueCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = text) (ha1 : reg m a1 = BitVec.ofNat 32 len) (ha2 : reg m a2 = out)
    (hlen : len < 2 ^ 32) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0)
    (sSC : Sep (reg m sp + 0xFFFFFFE0) 32 base tufHexDecodeCode.length)
    (sSV : Sep (reg m sp + 0xFFFFFFE0) 32 (base + 0x88) tufHexValueCode.length)
    (sST : Sep (reg m sp + 0xFFFFFFE0) 32 text len) (sSO : Sep (reg m sp + 0xFFFFFFE0) 32 out 128)
    (sOC : Sep out 128 base tufHexDecodeCode.length) (sOV : Sep out 128 (base + 0x88) tufHexValueCode.length)
    (sOT : Sep out 128 text len) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if (tufHexDecodeSpec m.mem text len).isSome then out else 0) ∧
      reg m' a1 = BitVec.ofNat 32 (len / 2) ∧
      (∀ bs, tufHexDecodeSpec m.mem text len = some bs →
        bs.length = len / 2 ∧ memBytes m'.mem out (len / 2) = bs) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFE0) 32 x 1 → Sep out 128 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R0, hR0⟩ : ∃ R0, reg m sp + 0xFFFFFFE0 = R0 := ⟨_, rfl⟩
  rw [hR0] at sSC sSV sST sSO ⊢
  have hR0a : R0.toNat % 4 = 0 := by rw [← hR0]; exact aligned_add hsp (k := 0xFFFFFFE0) (by decide)
  have al : ∀ c, c % 4 = 0 → (R0 + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hR0a h
  have stF : ∀ {M : Word → BitVec 8} (c : Nat) (v : Word), c + 4 ≤ 32 →
      (∀ x, Sep R0 32 x 1 → M x = m.mem x) →
      ∀ x, Sep R0 32 x 1 → memStore32 M (R0 + BitVec.ofNat 32 c) v x = m.mem x :=
    fun c _ hc4 hM x hx => by rw [memStore32_get_sep (hx.sub (c := c) (l := 4) hc4)]; exact hM x hx
  have cM : ∀ {M : Word → BitVec 8}, (∀ x, Sep R0 32 x 1 → M x = m.mem x) → CodeIn M base tufHexDecodeCode :=
    fun hM i hi => by rw [hM _ (sSC.subR (c := i) (l := 1) hi)]; exact hc i hi
  have ps : ∀ c d, d + 4 ≤ c → c + 4 ≤ 32 → Sep (R0 + BitVec.ofNat 32 d) 4 (R0 + BitVec.ofNat 32 c) 4 :=
    fun c d h1 h2 => sep_offsets R0 (Or.inl h1) (by omega) (by omega)
  -- a call of `tuf::hex_value`
  have callHV : ∀ {off : Nat} {o : Word} {n : Machine} {M : Word → BitVec 8} {c : Nat}, c < 256 →
      CodeIn M base tufHexDecodeCode → CodeIn M (base + 0x88) tufHexValueCode → St M base n off (reg n) →
      fetchRel tufHexDecodeCode off = some (.auipc ra 0x0, 4) →
      fetchRel tufHexDecodeCode (off + 4) = some (.jalr ra ra o, 4) →
      base + BitVec.ofNat 32 off + 0x0 + o = base + 0x88 → (off + 8) % 2 = 0 → reg n a0 = BitVec.ofNat 32 c →
      ∃ n', Steps n n' ∧ St M base n' (off + 8) (reg n') ∧ reg n' a0 = (if (hexDigit c).isSome then 1 else 0) ∧
        (∀ d, hexDigit c = some d → reg n' a1 = BitVec.ofNat 32 d) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ ra → reg n' q = reg n q := by
    intro off o n M c hc8 hcM hvM st h1 h2 hb he h0
    obtain ⟨c1, s1, pc1, mem1, regs1⟩ := st.callRa hcM h1 h2 hb (even_at base hbase 0x88 (by decide))
    have r1 := PEnv.reg1 regs1 st.zero
    obtain ⟨v, sv, pcv, memv, a0v, a1v, kv⟩ := tufHexValue_correct c1 hc8 (by rw [mem1]; exact hvM) pc1
      (by rw [r1 a0 (by decide), h0]) (by rw [regs1]; simp +decide [upd])
      (even_clear _ (even_at base hbase (off + 8) he))
    exact ⟨v, s1.trans sv, ⟨by rw [pcv], by rw [memv, mem1], fun _ => rfl⟩, a0v, a1v,
      fun q q0 q1 q2 q3 q4 q5 qr => by rw [kv q q0 q1 q2 q3 q4 q5, r1 q qr]⟩
  -- the prologue saves `ra` and `s0` through `s5`
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc thd_at_0 (off' := 2) (by decide)
  have g1 : reg n1 sp = R0 := by rw [ls_get u1 (by decide), ← hR0]; rfl
  have k1 : ∀ q, q ≠ sp → reg n1 q = reg m q := fun q h => ls_oth u1 h
  have kk1 : ∀ q, thdK q = true → reg n1 q = reg m q := ls_kst u1 (by decide) (fun _ _ => rfl)
  obtain ⟨n2, d2, u2⟩ := u1.self.sw hc thd_at_2 (off' := 4) (by decide) (by rw [g1]; exact al 28 (by decide))
  rw [g1, k1 ra (by decide), hra, show (0x1C : Word) = BitVec.ofNat 32 28 from rfl] at u2
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 m.mem (R0 + BitVec.ofNat 32 28) retAddr = M1 := ⟨_, rfl⟩
  rw [hM1] at u2
  have f1 : ∀ x, Sep R0 32 x 1 → M1 x = m.mem x := by rw [← hM1]; exact stF 28 _ (by decide) (fun _ _ => rfl)
  obtain ⟨n3, d3, u3⟩ := u2.sw (cM f1) thd_at_4 (off' := 6) (by decide) (by rw [g1]; exact al 24 (by decide))
  rw [g1, k1 8 (by decide), show (0x18 : Word) = BitVec.ofNat 32 24 from rfl] at u3
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 M1 (R0 + BitVec.ofNat 32 24) (reg m 8) = M2 := ⟨_, rfl⟩
  rw [hM2] at u3
  have f2 : ∀ x, Sep R0 32 x 1 → M2 x = m.mem x := by rw [← hM2]; exact stF 24 _ (by decide) f1
  obtain ⟨n4, d4, u4⟩ := u3.sw (cM f2) thd_at_6 (off' := 8) (by decide) (by rw [g1]; exact al 20 (by decide))
  rw [g1, k1 9 (by decide), show (0x14 : Word) = BitVec.ofNat 32 20 from rfl] at u4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 M2 (R0 + BitVec.ofNat 32 20) (reg m 9) = M3 := ⟨_, rfl⟩
  rw [hM3] at u4
  have f3 : ∀ x, Sep R0 32 x 1 → M3 x = m.mem x := by rw [← hM3]; exact stF 20 _ (by decide) f2
  obtain ⟨n5, d5, u5⟩ := u4.sw (cM f3) thd_at_8 (off' := 0xA) (by decide) (by rw [g1]; exact al 16 (by decide))
  rw [g1, k1 18 (by decide), show (0x10 : Word) = BitVec.ofNat 32 16 from rfl] at u5
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore32 M3 (R0 + BitVec.ofNat 32 16) (reg m 18) = M4 := ⟨_, rfl⟩
  rw [hM4] at u5
  have f4 : ∀ x, Sep R0 32 x 1 → M4 x = m.mem x := by rw [← hM4]; exact stF 16 _ (by decide) f3
  obtain ⟨n6, d6, u6⟩ := u5.sw (cM f4) thd_at_a (off' := 0xC) (by decide) (by rw [g1]; exact al 12 (by decide))
  rw [g1, k1 19 (by decide), show (0xC : Word) = BitVec.ofNat 32 12 from rfl] at u6
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 M4 (R0 + BitVec.ofNat 32 12) (reg m 19) = M5 := ⟨_, rfl⟩
  rw [hM5] at u6
  have f5 : ∀ x, Sep R0 32 x 1 → M5 x = m.mem x := by rw [← hM5]; exact stF 12 _ (by decide) f4
  obtain ⟨n7, d7, u7⟩ := u6.sw (cM f5) thd_at_c (off' := 0xE) (by decide) (by rw [g1]; exact al 8 (by decide))
  rw [g1, k1 20 (by decide), show (0x8 : Word) = BitVec.ofNat 32 8 from rfl] at u7
  obtain ⟨M6, hM6⟩ : ∃ M6, memStore32 M5 (R0 + BitVec.ofNat 32 8) (reg m 20) = M6 := ⟨_, rfl⟩
  rw [hM6] at u7
  have f6 : ∀ x, Sep R0 32 x 1 → M6 x = m.mem x := by rw [← hM6]; exact stF 8 _ (by decide) f5
  obtain ⟨n8, d8, u8⟩ := u7.sw (cM f6) thd_at_e (off' := 0x10) (by decide) (by rw [g1]; exact al 4 (by decide))
  rw [g1, k1 21 (by decide), show (0x4 : Word) = BitVec.ofNat 32 4 from rfl] at u8
  obtain ⟨M7, hM7⟩ : ∃ M7, memStore32 M6 (R0 + BitVec.ofNat 32 4) (reg m 21) = M7 := ⟨_, rfl⟩
  rw [hM7] at u8
  have f7 : ∀ x, Sep R0 32 x 1 → M7 x = m.mem x := by rw [← hM7]; exact stF 4 _ (by decide) f6
  have l28 : memLoad32 M7 (R0 + BitVec.ofNat 32 28) = retAddr := by
    rw [← hM7, memLoad32_store32_sep (ps 28 4 (by decide) (by decide)), ← hM6,
      memLoad32_store32_sep (ps 28 8 (by decide) (by decide)), ← hM5,
      memLoad32_store32_sep (ps 28 12 (by decide) (by decide)), ← hM4,
      memLoad32_store32_sep (ps 28 16 (by decide) (by decide)), ← hM3,
      memLoad32_store32_sep (ps 28 20 (by decide) (by decide)), ← hM2,
      memLoad32_store32_sep (ps 28 24 (by decide) (by decide)), ← hM1, memLoad32_store32_same]
  have l24 : memLoad32 M7 (R0 + BitVec.ofNat 32 24) = reg m 8 := by
    rw [← hM7, memLoad32_store32_sep (ps 24 4 (by decide) (by decide)), ← hM6,
      memLoad32_store32_sep (ps 24 8 (by decide) (by decide)), ← hM5,
      memLoad32_store32_sep (ps 24 12 (by decide) (by decide)), ← hM4,
      memLoad32_store32_sep (ps 24 16 (by decide) (by decide)), ← hM3,
      memLoad32_store32_sep (ps 24 20 (by decide) (by decide)), ← hM2, memLoad32_store32_same]
  have l20 : memLoad32 M7 (R0 + BitVec.ofNat 32 20) = reg m 9 := by
    rw [← hM7, memLoad32_store32_sep (ps 20 4 (by decide) (by decide)), ← hM6,
      memLoad32_store32_sep (ps 20 8 (by decide) (by decide)), ← hM5,
      memLoad32_store32_sep (ps 20 12 (by decide) (by decide)), ← hM4,
      memLoad32_store32_sep (ps 20 16 (by decide) (by decide)), ← hM3, memLoad32_store32_same]
  have l16 : memLoad32 M7 (R0 + BitVec.ofNat 32 16) = reg m 18 := by
    rw [← hM7, memLoad32_store32_sep (ps 16 4 (by decide) (by decide)), ← hM6,
      memLoad32_store32_sep (ps 16 8 (by decide) (by decide)), ← hM5,
      memLoad32_store32_sep (ps 16 12 (by decide) (by decide)), ← hM4, memLoad32_store32_same]
  have l12 : memLoad32 M7 (R0 + BitVec.ofNat 32 12) = reg m 19 := by
    rw [← hM7, memLoad32_store32_sep (ps 12 4 (by decide) (by decide)), ← hM6,
      memLoad32_store32_sep (ps 12 8 (by decide) (by decide)), ← hM5, memLoad32_store32_same]
  have l8 : memLoad32 M7 (R0 + BitVec.ofNat 32 8) = reg m 20 := by
    rw [← hM7, memLoad32_store32_sep (ps 8 4 (by decide) (by decide)), ← hM6, memLoad32_store32_same]
  have l4 : memLoad32 M7 (R0 + BitVec.ofNat 32 4) = reg m 21 := by
    rw [← hM7, memLoad32_store32_same]
  -- memory that matches `M7` outside `out`
  have cF : ∀ {M : Word → BitVec 8}, (∀ x, Sep out 128 x 1 → M x = M7 x) → CodeIn M base tufHexDecodeCode :=
    fun hF i hi => by
      rw [hF _ (sOC.subR (c := i) (l := 1) hi), f7 _ (sSC.subR (c := i) (l := 1) hi)]; exact hc i hi
  have vF : ∀ {M : Word → BitVec 8}, (∀ x, Sep out 128 x 1 → M x = M7 x) →
      CodeIn M (base + 0x88) tufHexValueCode := fun hF i hi => by
    rw [hF _ (sOV.subR (c := i) (l := 1) hi), f7 _ (sSV.subR (c := i) (l := 1) hi)]; exact hv i hi
  have tF : ∀ {M : Word → BitVec 8}, (∀ x, Sep out 128 x 1 → M x = M7 x) → ∀ i, i < len →
      M (text + BitVec.ofNat 32 i) = m.mem (text + BitVec.ofNat 32 i) := fun hF i hi => by
    rw [hF _ (sOT.subR (c := i) (l := 1) hi), f7 _ (sST.subR (c := i) (l := 1) hi)]
  have sF : ∀ {M : Word → BitVec 8}, (∀ x, Sep out 128 x 1 → M x = M7 x) → ∀ c, c + 4 ≤ 32 →
      memLoad32 M (R0 + BitVec.ofNat 32 c) = memLoad32 M7 (R0 + BitVec.ofNat 32 c) :=
    fun hF c hc4 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hF _ (sSO.sub (c := c + j) (l := 1) (by omega)).symm
  -- the epilogue at 0x26
  have tail : ∀ {n : Machine} {M : Word → BitVec 8}, (∀ x, Sep out 128 x 1 → M x = M7 x) →
      St M base n 0x26 (reg n) → reg n sp = R0 → (∀ q, thdK q = true → reg n q = reg m q) →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = M ∧ reg n' a0 = reg n 19 ∧ reg n' a1 = reg n 18 ∧
        (∀ q, thdK q = true → reg n' q = reg m q) ∧ (∀ q, thdS q = true → reg n' q = reg m q) := by
    intro n M hF st hs kk
    have hcM := cF hF
    obtain ⟨t1, e1, v1⟩ := st.alu hcM thd_at_26 (off' := 0x28) (by decide)
    obtain ⟨t2, e2, v2⟩ := v1.self.alu hcM thd_at_28 (off' := 0x2A) (by decide)
    have q2 : reg t2 sp = R0 := by rw [ls_oth v2 (show sp ≠ a1 by decide), ls_oth v1 (show sp ≠ a0 by decide), hs]
    obtain ⟨t3, e3, v3⟩ := v2.self.lw hcM thd_at_2a (off' := 0x2C) (by decide) (by rw [q2]; exact al 28 (by decide))
    rw [q2, show (0x1C : Word) = BitVec.ofNat 32 28 from rfl, sF hF 28 (by decide), l28] at v3
    have q3 : reg t3 sp = R0 := by rw [ls_oth v3 (show sp ≠ ra by decide), q2]
    obtain ⟨t4, e4, v4⟩ := v3.self.lw hcM thd_at_2c (off' := 0x2E) (by decide) (by rw [q3]; exact al 24 (by decide))
    rw [q3, show (0x18 : Word) = BitVec.ofNat 32 24 from rfl, sF hF 24 (by decide), l24] at v4
    have q4 : reg t4 sp = R0 := by rw [ls_oth v4 (show sp ≠ 8 by decide), q3]
    obtain ⟨t5, e5, v5⟩ := v4.self.lw hcM thd_at_2e (off' := 0x30) (by decide) (by rw [q4]; exact al 20 (by decide))
    rw [q4, show (0x14 : Word) = BitVec.ofNat 32 20 from rfl, sF hF 20 (by decide), l20] at v5
    have q5 : reg t5 sp = R0 := by rw [ls_oth v5 (show sp ≠ 9 by decide), q4]
    obtain ⟨t6, e6, v6⟩ := v5.self.lw hcM thd_at_30 (off' := 0x32) (by decide) (by rw [q5]; exact al 16 (by decide))
    rw [q5, show (0x10 : Word) = BitVec.ofNat 32 16 from rfl, sF hF 16 (by decide), l16] at v6
    have q6 : reg t6 sp = R0 := by rw [ls_oth v6 (show sp ≠ 18 by decide), q5]
    obtain ⟨t7, e7, v7⟩ := v6.self.lw hcM thd_at_32 (off' := 0x34) (by decide) (by rw [q6]; exact al 12 (by decide))
    rw [q6, show (0xC : Word) = BitVec.ofNat 32 12 from rfl, sF hF 12 (by decide), l12] at v7
    have q7 : reg t7 sp = R0 := by rw [ls_oth v7 (show sp ≠ 19 by decide), q6]
    obtain ⟨t8, e8, v8⟩ := v7.self.lw hcM thd_at_34 (off' := 0x36) (by decide) (by rw [q7]; exact al 8 (by decide))
    rw [q7, show (0x8 : Word) = BitVec.ofNat 32 8 from rfl, sF hF 8 (by decide), l8] at v8
    have q8 : reg t8 sp = R0 := by rw [ls_oth v8 (show sp ≠ 20 by decide), q7]
    obtain ⟨t9, e9, v9⟩ := v8.self.lw hcM thd_at_36 (off' := 0x38) (by decide) (by rw [q8]; exact al 4 (by decide))
    rw [q8, show (0x4 : Word) = BitVec.ofNat 32 4 from rfl, sF hF 4 (by decide), l4] at v9
    obtain ⟨t10, e10, v10⟩ := v9.self.aluImm hcM thd_at_38 (off' := 0x3A) (by decide)
    have w10 : reg t10 sp = reg m sp := by
      rw [ls_get v10 (by decide), ev_add, ls_oth v9 (show sp ≠ 21 by decide), q8, ← hR0, BitVec.add_assoc,
        show (0xFFFFFFE0 : Word) + 0x20 = 0 by decide, add_lit_zero]
    obtain ⟨t11, e11, pc11, mem11, regs11⟩ := v10.self.jalr hcM thd_at_3a
    have kk' : ∀ q, thdK q = true → reg t10 q = reg m q :=
      ls_kst v10 (by decide) (ls_kst v9 (by decide) (ls_kst v8 (by decide) (ls_kst v7 (by decide)
        (ls_kst v6 (by decide) (ls_kst v5 (by decide) (ls_kst v4 (by decide) (ls_kst v3 (by decide)
        (ls_kst v2 (by decide) (ls_kst v1 (by decide) kk)))))))))
    refine ⟨t11, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9
      (.cons e10 (.single e11)))))))))), ?_, mem11, ?_, ?_, fun q hq => by rw [regs11]; exact kk' q hq, ?_⟩
    · rw [pc11, ls_oth v10 (show ra ≠ sp by decide), ls_oth v9 (show ra ≠ 21 by decide),
        ls_oth v8 (show ra ≠ 20 by decide), ls_oth v7 (show ra ≠ 19 by decide), ls_oth v6 (show ra ≠ 18 by decide),
        ls_oth v5 (show ra ≠ 9 by decide), ls_oth v4 (show ra ≠ 8 by decide), ls_get v3 (by decide), add_lit_zero, hret]
    · rw [regs11, ls_oth v10 (show a0 ≠ sp by decide), ls_oth v9 (show a0 ≠ 21 by decide),
        ls_oth v8 (show a0 ≠ 20 by decide), ls_oth v7 (show a0 ≠ 19 by decide), ls_oth v6 (show a0 ≠ 18 by decide),
        ls_oth v5 (show a0 ≠ 9 by decide), ls_oth v4 (show a0 ≠ 8 by decide), ls_oth v3 (show a0 ≠ ra by decide),
        ls_oth v2 (show a0 ≠ a1 by decide), ls_get v1 (by decide), ls_r0]
      exact BitVec.zero_add _
    · rw [regs11, ls_oth v10 (show a1 ≠ sp by decide), ls_oth v9 (show a1 ≠ 21 by decide),
        ls_oth v8 (show a1 ≠ 20 by decide), ls_oth v7 (show a1 ≠ 19 by decide), ls_oth v6 (show a1 ≠ 18 by decide),
        ls_oth v5 (show a1 ≠ 9 by decide), ls_oth v4 (show a1 ≠ 8 by decide), ls_oth v3 (show a1 ≠ ra by decide),
        ls_get v2 (by decide), ls_r0, ls_oth v1 (show (18 : Fin 32) ≠ a0 by decide)]
      exact BitVec.zero_add _
    · intro q hq
      rcases thdS_cases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [regs11, ls_oth v10 (show ra ≠ sp by decide), ls_oth v9 (show ra ≠ 21 by decide),
          ls_oth v8 (show ra ≠ 20 by decide), ls_oth v7 (show ra ≠ 19 by decide), ls_oth v6 (show ra ≠ 18 by decide),
          ls_oth v5 (show ra ≠ 9 by decide), ls_oth v4 (show ra ≠ 8 by decide), ls_get v3 (by decide), hra]
      · rw [regs11, w10]
      · rw [regs11, ls_oth v10 (show (8 : Fin 32) ≠ sp by decide), ls_oth v9 (show (8 : Fin 32) ≠ 21 by decide),
          ls_oth v8 (show (8 : Fin 32) ≠ 20 by decide), ls_oth v7 (show (8 : Fin 32) ≠ 19 by decide),
          ls_oth v6 (show (8 : Fin 32) ≠ 18 by decide), ls_oth v5 (show (8 : Fin 32) ≠ 9 by decide),
          ls_get v4 (by decide)]
      · rw [regs11, ls_oth v10 (show (9 : Fin 32) ≠ sp by decide), ls_oth v9 (show (9 : Fin 32) ≠ 21 by decide),
          ls_oth v8 (show (9 : Fin 32) ≠ 20 by decide), ls_oth v7 (show (9 : Fin 32) ≠ 19 by decide),
          ls_oth v6 (show (9 : Fin 32) ≠ 18 by decide), ls_get v5 (by decide)]
      · rw [regs11, ls_oth v10 (show (18 : Fin 32) ≠ sp by decide), ls_oth v9 (show (18 : Fin 32) ≠ 21 by decide),
          ls_oth v8 (show (18 : Fin 32) ≠ 20 by decide), ls_oth v7 (show (18 : Fin 32) ≠ 19 by decide),
          ls_get v6 (by decide)]
      · rw [regs11, ls_oth v10 (show (19 : Fin 32) ≠ sp by decide), ls_oth v9 (show (19 : Fin 32) ≠ 21 by decide),
          ls_oth v8 (show (19 : Fin 32) ≠ 20 by decide), ls_get v7 (by decide)]
      · rw [regs11, ls_oth v10 (show (20 : Fin 32) ≠ sp by decide), ls_oth v9 (show (20 : Fin 32) ≠ 21 by decide),
          ls_get v8 (by decide)]
      · rw [regs11, ls_oth v10 (show (21 : Fin 32) ≠ sp by decide), ls_get v9 (by decide)]
  -- the `None` exit at 0x24
  have failP : ∀ {n : Machine} {M : Word → BitVec 8} {r : Option (List Nat)}, r = none →
      (∀ x, Sep out 128 x 1 → M x = M7 x) → St M base n 0x24 (reg n) → reg n sp = R0 →
      reg n 18 = BitVec.ofNat 32 (len / 2) → (∀ q, thdK q = true → reg n q = reg m q) →
      ThdPost m M7 retAddr out (len / 2) r n := by
    intro n M r hr hF st hs h18 kk
    obtain ⟨n1, d1, u1⟩ := st.aluImm (cF hF) thd_at_24 (off' := 0x26) (by decide)
    obtain ⟨n', c', pc', mem', a0', a1', kK, kS⟩ :=
      tail hF u1.self (by rw [ls_oth u1 (show sp ≠ 19 by decide), hs]) (ls_kst u1 (by decide) kk)
    refine ⟨n', .cons d1 c', pc', ?_, ?_, fun bs e => ?_, kK, kS, fun x hx => by rw [mem']; exact hF x hx⟩
    · rw [a0', ls_get u1 (by decide), ls_r0, hr]; rfl
    · rw [a1', ls_oth u1 (show (18 : Fin 32) ≠ 19 by decide), h18]
    · rw [hr] at e; cases e
  -- the `Some` exit at 0x26
  have doneP : ∀ {n : Machine} {M : Word → BitVec 8} {bs0 : List Nat}, (∀ x, Sep out 128 x 1 → M x = M7 x) →
      St M base n 0x26 (reg n) → reg n sp = R0 → reg n 18 = BitVec.ofNat 32 (len / 2) → reg n 19 = out →
      (∀ q, thdK q = true → reg n q = reg m q) → bs0.length = len / 2 → memBytes M out (len / 2) = bs0 →
      ThdPost m M7 retAddr out (len / 2) (some bs0) n := by
    intro n M bs0 hF st hs h18 h19 kk hl hm
    obtain ⟨n', c', pc', mem', a0', a1', kK, kS⟩ := tail hF st hs kk
    refine ⟨n', c', pc', by rw [a0', h19]; rfl, by rw [a1', h18], fun bs e => ?_, kK, kS,
      fun x hx => by rw [mem']; exact hF x hx⟩
    cases e
    exact ⟨hl, by rw [mem']; exact hm⟩
  -- setup: `s4 = out`, the parity of `len`, and `s2 = len / 2`
  obtain ⟨n9, d9, u9⟩ := u8.alu (cM f7) thd_at_10 (off' := 0x12) (by decide)
  have v9 : reg n9 20 = out := by
    rw [ls_get u9 (by decide), ls_r0, k1 a2 (by decide), ha2]; exact BitVec.zero_add _
  obtain ⟨n10, d10, u10⟩ := u9.self.aluImm (cM f7) thd_at_12 (off' := 0x16) (by decide)
  have v10 : reg n10 a2 = BitVec.ofNat 32 (len % 2) := by
    rw [ls_get u10 (by decide), ls_oth u9 (show a1 ≠ 20 by decide), k1 a1 (by decide), ha1]; exact thd_and1 hlen
  obtain ⟨n11, d11, u11⟩ := u10.self.aluImm (cM f7) thd_at_16 (off' := 0x1A) (by decide)
  have v11 : reg n11 18 = BitVec.ofNat 32 (len / 2) := by
    rw [ls_get u11 (by decide), ls_oth u10 (show a1 ≠ a2 by decide), ls_oth u9 (show a1 ≠ 20 by decide),
      k1 a1 (by decide), ha1]; exact thd_srl1 hlen
  have hs11 : reg n11 sp = R0 := by
    rw [ls_oth u11 (show sp ≠ 18 by decide), ls_oth u10 (show sp ≠ a2 by decide), ls_oth u9 (show sp ≠ 20 by decide), g1]
  have kk11 : ∀ q, thdK q = true → reg n11 q = reg m q :=
    ls_kst u11 (by decide) (ls_kst u10 (by decide) (ls_kst u9 (by decide) kk1))
  have pre11 : Steps m n11 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8
    (.cons d9 (.cons d10 (.single d11))))))))))
  suffices H : ThdPost m M7 retAddr out (len / 2) (tufHexDecodeSpec m.mem text len) n11 by
    obtain ⟨n', c', pc', a0', a1', bs', kK, kS, fr'⟩ := H
    refine ⟨n', pre11.trans c', pc', a0', a1', bs', fun r h0 h1 h2 h3 h4 h5 => ?_,
      fun x h1 h2 => by rw [fr' x h2, f7 x h1]⟩
    rcases thd_cover r h0 h1 h2 h3 h4 h5 with h | h
    · exact kK r h
    · exact kS r h
  by_cases hodd : len % 2 ≠ 0
  · -- odd length
    obtain ⟨n12, d12, u12⟩ := u11.self.taken (cM f7) 0x24 thd_at_1a (by decide) (by
      rw [ls_oth u11 (show a2 ≠ 18 by decide), v10, ls_r0]
      exact bne_iff_ne.mpr (by rw [show len % 2 = 1 by omega]; decide))
    have hnone : tufHexDecodeSpec m.mem text len = none := by
      unfold tufHexDecodeSpec
      by_cases h256 : len ≤ 256
      · rw [if_pos h256]; exact thd_odd (len / 2) _ (by rw [memBytes_length]; omega)
      · rw [if_neg h256]
    exact ThdPost.pre (failP hnone (fun _ _ => rfl) u12.self (by rw [u12.regs, hs11]) (by rw [u12.regs, v11])
      (fun q hq => by rw [u12.regs]; exact kk11 q hq)) (.single d12)
  have hev : len % 2 = 0 := Decidable.of_not_not hodd
  clear hodd
  obtain ⟨n12, d12, u12⟩ := u11.self.notTaken (cM f7) 0x1C thd_at_1a (by decide) (by
    rw [ls_oth u11 (show a2 ≠ 18 by decide), v10, ls_r0, show len % 2 = 0 by omega]; rfl)
  obtain ⟨n13, d13, u13⟩ := u12.aluImm (cM f7) thd_at_1c (off' := 0x20) (by decide)
  have v13 : reg n13 a2 = BitVec.ofNat 32 257 := by rw [ls_get u13 (by decide), ls_r0]; rfl
  have a113 : reg n13 a1 = BitVec.ofNat 32 len := by
    rw [ls_oth u13 (show a1 ≠ a2 by decide), ls_oth u11 (show a1 ≠ 18 by decide),
      ls_oth u10 (show a1 ≠ a2 by decide), ls_oth u9 (show a1 ≠ 20 by decide), k1 a1 (by decide), ha1]
  have kk13 : ∀ q, thdK q = true → reg n13 q = reg m q := ls_kst u13 (by decide) kk11
  by_cases hbig : 257 < len
  · -- too long for `out`
    obtain ⟨n14, d14, u14⟩ := u13.self.notTaken (cM f7) 0x24 thd_at_20 (by decide) (by
      rw [ls_uge, v13, a113, ls_ofNat_toNat_lt (c := 257) (by decide), ls_ofNat_toNat_lt hlen,
        decide_eq_true (by omega)]; try rfl)
    have hnone : tufHexDecodeSpec m.mem text len = none := by
      unfold tufHexDecodeSpec; rw [if_neg (by omega)]
    exact ThdPost.pre (failP hnone (fun _ _ => rfl) u14.self
      (by rw [u14.regs, ls_oth u13 (show sp ≠ a2 by decide), hs11])
      (by rw [u14.regs, ls_oth u13 (show (18 : Fin 32) ≠ a2 by decide), v11])
      (fun q hq => by rw [u14.regs]; exact kk13 q hq)) (.cons d12 (.cons d13 (.single d14)))
  have hfit : len ≤ 257 := Nat.le_of_not_lt hbig
  clear hbig
  obtain ⟨n14, d14, u14⟩ := u13.self.taken (cM f7) 0x3C thd_at_20 (by decide) (by
    rw [ls_uge, v13, a113, ls_ofNat_toNat_lt (c := 257) (by decide), ls_ofNat_toNat_lt hlen,
      decide_eq_false (by omega)]; try rfl)
  obtain ⟨n15, d15, u15⟩ := u14.aluImm (cM f7) thd_at_3c (off' := 0x40) (by decide)
  obtain ⟨n16, d16, u16⟩ := u15.self.alu (cM f7) thd_at_40 (off' := 0x44) (by decide)
  obtain ⟨n17, d17, u17⟩ := u16.self.alu (cM f7) thd_at_44 (off' := 0x48) (by decide)
  have hu : (BitVec.ofNat 32 len).ult 0x102 = true :=
    decide_eq_true (by rw [ls_ofNat_toNat_lt hlen]; show len < 258; omega)
  have hslt : aluEval .sltu (BitVec.ofNat 32 len) 0x102 = 1 := by
    show (if (BitVec.ofNat 32 len).ult 0x102 = true then (1 : Word) else 0) = 1
    rw [if_pos hu]
  have v17 : reg n17 19 = out := by
    rw [ls_get u17 (by decide), ls_get u16 (by decide), ls_oth u16 (show (20 : Fin 32) ≠ a1 by decide), ls_r0,
      ls_get u15 (by decide), ls_oth u15 (show (20 : Fin 32) ≠ a1 by decide), a113, hslt,
      ls_oth u13 (show (20 : Fin 32) ≠ a2 by decide), ls_oth u11 (show (20 : Fin 32) ≠ 18 by decide),
      ls_oth u10 (show (20 : Fin 32) ≠ a2 by decide), v9]
    exact ls_ones_and out
  obtain ⟨n18, d18, u18⟩ := u17.self.aluImm (cM f7) thd_at_48 (off' := 0x4C) (by decide)
  obtain ⟨n19, d19, u19⟩ := u18.self.alu (cM f7) thd_at_4c (off' := 0x4E) (by decide)
  have kk19 : ∀ q, thdK q = true → reg n19 q = reg m q :=
    ls_kst u19 (by decide) (ls_kst u18 (by decide) (ls_kst u17 (by decide) (ls_kst u16 (by decide)
      (ls_kst u15 (by decide) kk13))))
  have w18 : reg n19 18 = BitVec.ofNat 32 (len / 2) := by
    rw [ls_oth u19 (show (18 : Fin 32) ≠ 21 by decide), ls_oth u18 (show (18 : Fin 32) ≠ 9 by decide),
      ls_oth u17 (show (18 : Fin 32) ≠ 19 by decide), ls_oth u16 (show (18 : Fin 32) ≠ a1 by decide),
      ls_oth u15 (show (18 : Fin 32) ≠ a1 by decide), ls_oth u13 (show (18 : Fin 32) ≠ a2 by decide), v11]
  have w19 : reg n19 19 = out := by
    rw [ls_oth u19 (show (19 : Fin 32) ≠ 21 by decide), ls_oth u18 (show (19 : Fin 32) ≠ 9 by decide), v17]
  have w9 : reg n19 9 = text + BitVec.ofNat 32 (2 * 0 + 1) := by
    rw [ls_oth u19 (show (9 : Fin 32) ≠ 21 by decide), ls_get u18 (by decide),
      ls_oth u17 (show a0 ≠ 19 by decide), ls_oth u16 (show a0 ≠ a1 by decide), ls_oth u15 (show a0 ≠ a1 by decide),
      ls_oth u13 (show a0 ≠ a2 by decide), ls_oth u11 (show a0 ≠ 18 by decide), ls_oth u10 (show a0 ≠ a2 by decide),
      ls_oth u9 (show a0 ≠ 20 by decide), k1 a0 (by decide), ha0]
    rfl
  have w20 : reg n19 20 = out := by
    rw [ls_oth u19 (show (20 : Fin 32) ≠ 21 by decide), ls_oth u18 (show (20 : Fin 32) ≠ 9 by decide),
      ls_oth u17 (show (20 : Fin 32) ≠ 19 by decide), ls_oth u16 (show (20 : Fin 32) ≠ a1 by decide),
      ls_oth u15 (show (20 : Fin 32) ≠ a1 by decide), ls_oth u13 (show (20 : Fin 32) ≠ a2 by decide),
      ls_oth u11 (show (20 : Fin 32) ≠ 18 by decide), ls_oth u10 (show (20 : Fin 32) ≠ a2 by decide), v9]
  have w21 : reg n19 21 = BitVec.ofNat 32 (len / 2) := by
    rw [ls_get u19 (by decide), ls_r0, ls_oth u18 (show (18 : Fin 32) ≠ 9 by decide),
      ls_oth u17 (show (18 : Fin 32) ≠ 19 by decide), ls_oth u16 (show (18 : Fin 32) ≠ a1 by decide),
      ls_oth u15 (show (18 : Fin 32) ≠ a1 by decide), ls_oth u13 (show (18 : Fin 32) ≠ a2 by decide), v11]
    exact BitVec.zero_add _
  have wsp : reg n19 sp = R0 := by
    rw [ls_oth u19 (show sp ≠ 21 by decide), ls_oth u18 (show sp ≠ 9 by decide), ls_oth u17 (show sp ≠ 19 by decide),
      ls_oth u16 (show sp ≠ a1 by decide), ls_oth u15 (show sp ≠ a1 by decide), ls_oth u13 (show sp ≠ a2 by decide),
      hs11]
  have hspec : tufHexDecodeSpec m.mem text len = parseHex (memBytes m.mem text len) := by
    unfold tufHexDecodeSpec; rw [if_pos (by omega)]
  rw [hspec]
  rcases Nat.eq_zero_or_pos (len / 2) with h0 | hpos
  · -- empty text
    obtain ⟨n20, d20, u20⟩ := u19.self.taken (cM f7) 0x26 thd_at_4e (by decide) (by rw [w18, h0]; rfl)
    have hS : parseHex (memBytes m.mem text len) = some [] := by rw [show len = 0 by omega]; rfl
    rw [hS]
    exact ThdPost.pre (doneP (fun _ _ => rfl) u20.self (by rw [u20.regs, wsp]) (by rw [u20.regs, w18])
      (by rw [u20.regs, w19]) (fun q hq => by rw [u20.regs]; exact kk19 q hq) (by rw [h0]; rfl)
      (by rw [h0]; rfl))
      (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.single d20)))))))))
  obtain ⟨n20, d20, u20⟩ := u19.self.notTaken (cM f7) 0x52 thd_at_4e (by decide) (by
    rw [w18, ls_r0]; exact beq_false_of_ne (thd_ne0 hpos (by omega)))
  have eSp : reg n20 sp = R0 := by rw [u20.regs, wsp]
  have e18 : reg n20 18 = BitVec.ofNat 32 (len / 2) := by rw [u20.regs, w18]
  have eK : ∀ q, thdK q = true → reg n20 q = reg m q := fun q hq => by rw [u20.regs]; exact kk19 q hq
  have e19 : reg n20 19 = out := by rw [u20.regs, w19]
  -- one pass of the loop at 0x52, which decodes byte `k` with `d + 1` bytes left
  have body : ∀ (d k : Nat) {n : Machine} {Mk : Word → BitVec 8} {bsk : List Nat}, k + (d + 1) = len / 2 →
      St Mk base n 0x52 (reg n) → (∀ x, Sep out 128 x 1 → Mk x = M7 x) → memBytes Mk out k = bsk →
      reg n 9 = text + BitVec.ofNat 32 (2 * k + 1) → reg n 20 = out + BitVec.ofNat 32 k →
      reg n 21 = BitVec.ofNat 32 (d + 1) → (∀ q, thdL q = true → reg n q = reg n20 q) →
      parseHex (memBytes m.mem text len) =
        (parseHex (memBytes m.mem (text + BitVec.ofNat 32 (2 * k)) (2 * (d + 1)))).map (bsk ++ ·) →
      ThdPost m M7 retAddr out (len / 2) (parseHex (memBytes m.mem text len)) n ∨
      ∃ n2 Mk2 bsk2, Steps n n2 ∧ St Mk2 base n2 0x82 (reg n2) ∧ (∀ x, Sep out 128 x 1 → Mk2 x = M7 x) ∧
        memBytes Mk2 out (k + 1) = bsk2 ∧ reg n2 9 = text + BitVec.ofNat 32 (2 * (k + 1) + 1) ∧
        reg n2 20 = out + BitVec.ofNat 32 (k + 1) ∧ reg n2 21 = BitVec.ofNat 32 d ∧
        (∀ q, thdL q = true → reg n2 q = reg n20 q) ∧
        parseHex (memBytes m.mem text len) =
          (parseHex (memBytes m.mem (text + BitVec.ofNat 32 (2 * (k + 1))) (2 * d))).map (bsk2 ++ ·) := by
    intro d k n Mk bsk hk st hF hB h9 h20 h21 hL hS
    have hcM := cF hF
    have hvM := vF hF
    have hk2 : 2 * k + 1 < len := by omega
    have nsp : reg n sp = R0 := by rw [hL sp (by decide), eSp]
    have n18 : reg n 18 = BitVec.ofNat 32 (len / 2) := by rw [hL 18 (by decide), e18]
    have nK : ∀ q, thdK q = true → reg n q = reg m q := fun q hq => by rw [hL q (thdK_L q hq), eK q hq]
    -- the high digit
    obtain ⟨w1, x1, y1⟩ := st.lbu hcM thd_at_52 (off' := 0x56) (by decide)
    obtain ⟨cH, hcH⟩ : ∃ c, (m.mem (text + BitVec.ofNat 32 (2 * k))).toNat = c := ⟨_, rfl⟩
    have a0w1 : reg w1 a0 = BitVec.ofNat 32 cH := by
      rw [ls_get y1 (by decide), h9, BitVec.add_assoc, thd_dec' (j := 2 * k + 1) (by omega) (by omega),
        show 2 * k + 1 - 1 = 2 * k by omega, tF hF (2 * k) (by omega), thd_zext, hcH]
    have jK1 : ∀ q, thdJ q = true → reg w1 q = reg n q := ls_kst y1 (by decide) (fun _ _ => rfl)
    obtain ⟨w2, x2, y2, f2a0, f2a1, k2⟩ := callHV (by rw [← hcH]; exact (m.mem _).isLt) hcM hvM y1.self
      thd_at_56 thd_at_5a (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) a0w1
    have jK2 : ∀ q, thdJ q = true → reg w2 q = reg n q := fun q hq => by
      obtain ⟨h0, h1, h2, h3, h4, h5, hr⟩ := thdJ_ne q hq; rw [k2 q h0 h1 h2 h3 h4 h5 hr]; exact jK1 q hq
    obtain ⟨w3, x3, y3⟩ := y2.aluImm hcM thd_at_5e (off' := 0x60) (by decide)
    have a0w3 : reg w3 a0 = if (hexDigit cH).isSome then 1 else 0 := by
      rw [ls_get y3 (by decide), f2a0]; exact thd_flag _
    have jK3 := ls_kst y3 (by decide) jK2
    have hS1 := hS
    rw [thd_stepAt, hcH] at hS1
    cases hh : hexDigit cH with
    | none =>
      left
      obtain ⟨w4, x4, y4⟩ := y3.self.taken hcM 0x24 thd_at_60 (by decide) (by rw [a0w3, ls_r0, hh]; rfl)
      have jK4 : ∀ q, thdJ q = true → reg w4 q = reg n q := fun q hq => by rw [y4.regs]; exact jK3 q hq
      refine ThdPost.pre (failP (by rw [hS1, hh]; try rfl) hF y4.self ?_ ?_ ?_)
        (.cons x1 (x2.trans (.cons x3 (.single x4))))
      · rw [jK4 sp (by decide), nsp]
      · rw [jK4 18 (by decide), n18]
      · intro q hq; rw [jK4 q (thdL_J q (thdK_L q hq)), nK q hq]
    | some h =>
      have hh16 : h < 16 := thd_digit hh
      obtain ⟨w4, x4, y4⟩ := y3.self.notTaken hcM 0x62 thd_at_60 (by decide) (by rw [a0w3, ls_r0, hh]; rfl)
      obtain ⟨w5, x5, y5⟩ := y4.alu hcM thd_at_62 (off' := 0x64) (by decide)
      have s0w5 : reg w5 8 = BitVec.ofNat 32 h := by
        rw [ls_get y5 (by decide), ls_r0, ls_oth y3 (show a1 ≠ a0 by decide), f2a1 h hh]; exact BitVec.zero_add _
      have jK5 := ls_kst y5 (by decide) jK3
      -- the low digit
      obtain ⟨w6, x6, y6⟩ := y5.self.lbu hcM thd_at_64 (off' := 0x68) (by decide)
      obtain ⟨cL, hcL⟩ : ∃ c, (m.mem (text + BitVec.ofNat 32 (2 * k + 1))).toNat = c := ⟨_, rfl⟩
      have a0w6 : reg w6 a0 = BitVec.ofNat 32 cL := by
        rw [ls_get y6 (by decide), ls_oth y5 (show (9 : Fin 32) ≠ 8 by decide), jK3 9 (by decide), h9,
          add_lit_zero, tF hF (2 * k + 1) hk2, thd_zext, hcL]
      have jK6 := ls_kst y6 (by decide) jK5
      obtain ⟨w7, x7, y7, f7a0, f7a1, k7⟩ := callHV (by rw [← hcL]; exact (m.mem _).isLt) hcM hvM y6.self
        thd_at_68 thd_at_6c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) a0w6
      have jK7 : ∀ q, thdJ q = true → reg w7 q = reg n q := fun q hq => by
        obtain ⟨h0, h1, h2, h3, h4, h5, hr⟩ := thdJ_ne q hq; rw [k7 q h0 h1 h2 h3 h4 h5 hr]; exact jK6 q hq
      have s0w7 : reg w7 8 = BitVec.ofNat 32 h := by
        rw [k7 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          ls_oth y6 (show (8 : Fin 32) ≠ a0 by decide), s0w5]
      obtain ⟨w8, x8, y8⟩ := y7.aluImm hcM thd_at_70 (off' := 0x72) (by decide)
      have a0w8 : reg w8 a0 = if (hexDigit cL).isSome then 1 else 0 := by
        rw [ls_get y8 (by decide), f7a0]; exact thd_flag _
      have jK8 := ls_kst y8 (by decide) jK7
      cases hl : hexDigit cL with
      | none =>
        left
        obtain ⟨w9, x9, y9⟩ := y8.self.taken hcM 0x24 thd_at_72 (by decide) (by rw [a0w8, ls_r0, hl]; rfl)
        have jK9 : ∀ q, thdJ q = true → reg w9 q = reg n q := fun q hq => by rw [y9.regs]; exact jK8 q hq
        refine ThdPost.pre (failP (by rw [hS1, hh, hcL, hl]; try rfl) hF y9.self ?_ ?_ ?_)
          (.cons x1 (x2.trans (.cons x3 (.cons x4 (.cons x5 (.cons x6 (x7.trans (.cons x8 (.single x9)))))))))
        · rw [jK9 sp (by decide), nsp]
        · rw [jK9 18 (by decide), n18]
        · intro q hq; rw [jK9 q (thdL_J q (thdK_L q hq)), nK q hq]
      | some l =>
        right
        have hl16 : l < 16 := thd_digit hl
        obtain ⟨w9, x9, y9⟩ := y8.self.notTaken hcM 0x74 thd_at_72 (by decide) (by rw [a0w8, ls_r0, hl]; rfl)
        obtain ⟨w10, x10, y10⟩ := y9.aluImm hcM thd_at_74 (off' := 0x76) (by decide)
        obtain ⟨w11, x11, y11⟩ := y10.self.alu hcM thd_at_76 (off' := 0x78) (by decide)
        have a1w11 : reg w11 a1 = aluEval .or (BitVec.ofNat 32 l) (aluEval .sll (BitVec.ofNat 32 h) 4) := by
          rw [ls_get y11 (by decide), ls_get y10 (by decide), ls_oth y10 (show a1 ≠ 8 by decide),
            ls_oth y8 (show a1 ≠ a0 by decide), ls_oth y8 (show (8 : Fin 32) ≠ a0 by decide), f7a1 l hl, s0w7]
        have jK11 := ls_kst y11 (by decide) (ls_kst y10 (by decide) jK8)
        have s4w11 : reg w11 20 = out + BitVec.ofNat 32 k := by rw [jK11 20 (by decide), h20]
        -- the store of byte `k`
        obtain ⟨w12, x12, y12⟩ := y11.self.sb hcM thd_at_78 (off' := 0x7C) (by decide)
        rw [s4w11, add_lit_zero, a1w11] at y12
        obtain ⟨Mk2, hMk2⟩ : ∃ M2, memStore8 Mk (out + BitVec.ofNat 32 k)
            ((aluEval .or (BitVec.ofNat 32 l) (aluEval .sll (BitVec.ofNat 32 h) 4)).extractLsb' 0 8) = M2 :=
          ⟨_, rfl⟩
        rw [hMk2] at y12
        have hk128 : k < 128 := by omega
        have hF2 : ∀ x, Sep out 128 x 1 → Mk2 x = M7 x := fun x hx => by
          rw [← hMk2, thd_st8_ne (ls_sep_ne hx hk128)]; exact hF x hx
        have hcM2 := cF hF2
        obtain ⟨w13, x13, y13⟩ := y12.aluImm hcM2 thd_at_7c (off' := 0x7E) (by decide)
        obtain ⟨w14, x14, y14⟩ := y13.self.aluImm hcM2 thd_at_7e (off' := 0x80) (by decide)
        obtain ⟨w15, x15, y15⟩ := y14.self.aluImm hcM2 thd_at_80 (off' := 0x82) (by decide)
        have hne : ∀ i, i < k → out + BitVec.ofNat 32 i ≠ out + BitVec.ofNat 32 k := fun i hi e => by
          have := sep_offsets out (c := i) (n := 1) (d := k) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
          exact this 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e)
        refine ⟨w15, Mk2, bsk ++ [16 * h + l], .cons x1 (x2.trans (.cons x3 (.cons x4 (.cons x5 (.cons x6
          (x7.trans (.cons x8 (.cons x9 (.cons x10 (.cons x11 (.cons x12 (.cons x13 (.cons x14
          (.single x15)))))))))))))), y15.self, hF2, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [thd_snoc, memBytes_congr (M := Mk) (fun i hi => by rw [← hMk2, thd_st8_ne (hne i hi)]), hB,
            ← hMk2, thd_st8_eq]
          exact congrArg (fun t => bsk ++ [t]) (thd_byte ⟨h, hh16⟩ ⟨l, hl16⟩)
        · rw [ls_oth y15 (show (9 : Fin 32) ≠ 21 by decide), ls_get y14 (by decide),
            ls_oth y13 (show (9 : Fin 32) ≠ 20 by decide), jK11 9 (by decide), h9, ev_add,
            show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega]
        · rw [ls_oth y15 (show (20 : Fin 32) ≠ 21 by decide), ls_oth y14 (show (20 : Fin 32) ≠ 9 by decide),
            ls_get y13 (by decide), s4w11, ev_add, show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]
        · rw [ls_get y15 (by decide), ls_oth y14 (show (21 : Fin 32) ≠ 9 by decide),
            ls_oth y13 (show (21 : Fin 32) ≠ 20 by decide), jK11 21 (by decide), h21, ev_add,
            thd_dec' (j := d + 1) (by omega) (by omega), Nat.add_sub_cancel]
        · have lK11 : ∀ q, thdL q = true → reg w11 q = reg n20 q := fun q hq => by
            rw [jK11 q (thdL_J q hq), hL q hq]
          exact ls_kst y15 (by decide) (ls_kst y14 (by decide) (ls_kst y13 (by decide) lK11))
        · rw [hS1, hh, hcL, hl]
          exact thd_map_snoc _ bsk (16 * h + l)
  have loop : ∀ (d k : Nat) {n : Machine} {Mk : Word → BitVec 8} {bsk : List Nat}, k + (d + 1) = len / 2 →
      St Mk base n 0x52 (reg n) → (∀ x, Sep out 128 x 1 → Mk x = M7 x) → memBytes Mk out k = bsk →
      reg n 9 = text + BitVec.ofNat 32 (2 * k + 1) → reg n 20 = out + BitVec.ofNat 32 k →
      reg n 21 = BitVec.ofNat 32 (d + 1) → (∀ q, thdL q = true → reg n q = reg n20 q) →
      parseHex (memBytes m.mem text len) =
        (parseHex (memBytes m.mem (text + BitVec.ofNat 32 (2 * k)) (2 * (d + 1)))).map (bsk ++ ·) →
      ThdPost m M7 retAddr out (len / 2) (parseHex (memBytes m.mem text len)) n := by
    intro d
    induction d with
    | zero =>
      intro k n Mk bsk hk st hF hB h9 h20 h21 hL hS
      rcases body 0 k hk st hF hB h9 h20 h21 hL hS with hp | ⟨n2, Mk2, bsk2, c2, st2, hF2, hB2, -, -, h21', hL2, hS2⟩
      · exact hp
      · obtain ⟨n3, d3, u3⟩ := st2.taken (cF hF2) 0x26 thd_at_82 (by decide) (by rw [h21', ls_r0]; rfl)
        have hS3 : parseHex (memBytes m.mem text len) = some bsk2 := by
          rw [hS2]; exact congrArg some (List.append_nil bsk2)
        rw [hS3]
        refine ThdPost.pre (doneP hF2 u3.self ?_ ?_ ?_ ?_ ?_ ?_) (c2.trans (.single d3))
        · rw [u3.regs, hL2 sp (by decide), eSp]
        · rw [u3.regs, hL2 18 (by decide), e18]
        · rw [u3.regs, hL2 19 (by decide), e19]
        · intro q hq; rw [u3.regs, hL2 q (thdK_L q hq), eK q hq]
        · rw [← hB2, memBytes_length]; omega
        · rw [show len / 2 = k + 1 by omega]; exact hB2
    | succ d ih =>
      intro k n Mk bsk hk st hF hB h9 h20 h21 hL hS
      rcases body (d + 1) k hk st hF hB h9 h20 h21 hL hS with
        hp | ⟨n2, Mk2, bsk2, c2, st2, hF2, hB2, h9', h20', h21', hL2, hS2⟩
      · exact hp
      · obtain ⟨n3, d3, u3⟩ := st2.notTaken (cF hF2) 0x86 thd_at_82 (by decide) (by
          rw [h21', ls_r0]; exact beq_false_of_ne (thd_ne0 (by omega) (by omega)))
        obtain ⟨n4, d4, u4⟩ := u3.jump (cF hF2) thd_at_86 (off' := 0x52) (by decide) (by
          rw [u3.pc]; exact ls_even hbase 0x86 0xFFFFFFCC 0x52 (by decide) (by decide))
        exact (ih (k + 1) (by omega) u4.self hF2 hB2 (by rw [u4.regs, h9']) (by rw [u4.regs, h20'])
          (by rw [u4.regs, h21']) (fun q hq => by rw [u4.regs, hL2 q hq]) hS2).pre
          (c2.trans (.cons d3 (.single d4)))
  obtain ⟨d, hd⟩ : ∃ d, len / 2 = d + 1 := ⟨len / 2 - 1, by omega⟩
  exact (loop d 0 (by omega) u20.self (fun _ _ => rfl) rfl (by rw [u20.regs, w9])
    (by rw [u20.regs, w20, add_ofNat_zero]) (by rw [u20.regs, w21, hd]) (fun _ _ => rfl)
    (by rw [memBytes_zero, thd_map_nil, show 2 * 0 = 0 from rfl, add_ofNat_zero, show 2 * (d + 1) = len by omega])).pre
    (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.single d20)))))))))

end C3.RV32
