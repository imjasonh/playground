import C3BootProofs.Proofs.JsonMembers
import C3BootProofs.Proofs.JsonLiteralEnd

/-!
# `json::read_item`, as compiled

`read_item(doc, pos)` finds the end of the value at `pos` the way
`value_end` does, then skips the whitespace after it and one comma with the
whitespace after that. It stores `Ok((value, after))`, the value as a slice
of `doc` and `after` as a position, or `Err(Json)`, at `out`. The compiled
function inlines `value_end`: a string, a literal, or a number goes to its
scanner, and an object or an array is scanned byte by byte with a depth
counter, skipping strings with `string_end` in canonical mode.

It saves `ra` and `s0`–`s5` in a 48-byte frame. `literal_end` pushes 68
more bytes, so the stack region is the 116 bytes below `sp`. The result has
the layout `CurRes` describes: the slice's pointer at `out`, its length at
`out + 4`, and `after` at `out + 8`, or a null pointer with the error byte
`0x20` at `out + 4`.

`cScan`, `valueEnd`, and `readItem` say what the function computes.
-/

namespace C3.Json

/-- The scan of an object or array from `i` at nesting `depth`, with `k`
steps left: the position after the bracket that closes it. -/
def cScan (d : Bytes) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | k + 1, depth, i =>
    if d.length ≤ i then none
    else if d.getD i 0 = 34 then (stringEnd true d i).bind (cScan d k depth)
    else if d.getD i 0 = 91 ∨ d.getD i 0 = 123 then cScan d k (depth + 1) (i + 1)
    else if d.getD i 0 = 93 ∨ d.getD i 0 = 125 then
      (if depth = 0 then none else if depth = 1 then some (i + 1) else cScan d k (depth - 1) (i + 1))
    else cScan d k depth (i + 1)

/-- `value_end`: the position after the value at `pos`. -/
def valueEnd (d : Bytes) (pos : Nat) : Option Nat :=
  if d.length ≤ pos then none
  else if d.getD pos 0 = 34 then stringEnd true d pos
  else if d.getD pos 0 = 91 ∨ d.getD pos 0 = 123 then cScan d (d.length + 1) 0 pos
  else if d.getD pos 0 = 102 ∨ d.getD pos 0 = 110 ∨ d.getD pos 0 = 116 then literalEnd d pos
  else if isDigit (d.getD pos 0) then numberEnd d pos
  else none

/-- The value's end `e` and the position after the whitespace, comma, and
whitespace that follow it. -/
def itemTail (d : Bytes) (e : Nat) : Nat × Nat :=
  if skipWs d e < d.length ∧ d.getD (skipWs d e) 0 = 44 then (e, skipWs d (skipWs d e + 1))
  else (e, skipWs d e)

/-- `read_item`: the end of the value at `pos` and the position after it. -/
def readItem (d : Bytes) (pos : Nat) : Option (Nat × Nat) := (valueEnd d pos).map (itemTail d)

theorem stringEnd_gt {c : Bool} {d : Bytes} {pos e : Nat} (h : stringEnd c d pos = some e) : pos < e := by
  unfold stringEnd at h
  split at h
  · cases h
  · obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h
    omega

theorem litScan_bd {rest : Bytes} {pos e : Nat} :
    ∀ {ws : List Bytes}, (∀ w, w ∈ ws → w ≠ []) → litScan rest pos ws = some e →
      pos < e ∧ e ≤ pos + rest.length
  | [], _, h => by cases h
  | w :: ws, hne, h => by
    simp only [litScan] at h
    split at h
    · rename_i hw
      cases h
      have : w.length ≠ 0 := fun h0 => hne w (List.mem_cons_self ..) (List.eq_nil_of_length_eq_zero h0)
      omega
    · exact litScan_bd (fun w' hw' => hne w' (List.mem_cons_of_mem _ hw')) h

theorem literalEnd_bd {d : Bytes} {pos e : Nat} (h : literalEnd d pos = some e) : pos < e ∧ e ≤ d.length := by
  unfold literalEnd at h
  split at h
  · cases h
  · have := litScan_bd (ws := litWords) (by decide) h
    rw [List.length_drop] at this
    omega

theorem numberEnd_bd {d : Bytes} {pos e : Nat} (h : numberEnd d pos = some e) : pos < e ∧ e ≤ d.length := by
  have hl := digLen_le (d.drop pos)
  rw [List.length_drop] at hl
  unfold numberEnd at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · split at h
          · cases h; omega
          · cases h
        · cases h; omega

theorem cScan_bd {d : Bytes} : ∀ {k depth i e : Nat}, cScan d k depth i = some e → i < e ∧ e ≤ d.length
  | 0, _, _, _, h => by cases h
  | k + 1, depth, i, e, h => by
    simp only [cScan] at h
    split at h
    · cases h
    split at h
    · obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.mp h
      have := stringEnd_gt hj
      have := cScan_bd h
      omega
    split at h
    · have := cScan_bd h; omega
    split at h
    · split at h
      · cases h
      split at h
      · cases h; omega
      · have := cScan_bd h; omega
    · have := cScan_bd h; omega

theorem valueEnd_bd {d : Bytes} {pos e : Nat} (h : valueEnd d pos = some e) : pos < e ∧ e ≤ d.length := by
  unfold valueEnd at h
  split at h
  · cases h
  split at h
  · exact ⟨stringEnd_gt h, stringEnd_le h⟩
  split at h
  · exact cScan_bd h
  split at h
  · exact literalEnd_bd h
  split at h
  · exact numberEnd_bd h
  · cases h

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem ri_at_0 : fetchRel jsonReadItemCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem ri_at_2 : fetchRel jsonReadItemCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem ri_at_4 : fetchRel jsonReadItemCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem ri_at_6 : fetchRel jsonReadItemCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem ri_at_8 : fetchRel jsonReadItemCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem ri_at_a : fetchRel jsonReadItemCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem ri_at_c : fetchRel jsonReadItemCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem ri_at_e : fetchRel jsonReadItemCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem ri_at_10 : fetchRel jsonReadItemCode 0x10 = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem ri_at_12 : fetchRel jsonReadItemCode 0x12 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem ri_at_14 : fetchRel jsonReadItemCode 0x14 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem ri_at_16 : fetchRel jsonReadItemCode 0x16 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem ri_at_18 : fetchRel jsonReadItemCode 0x18 = some (.alu .add (20 : Fin 32) a1 a3, 4) := by decide
theorem ri_at_1c : fetchRel jsonReadItemCode 0x1C = some (.branch .bgeu a3 a2 0xBA, 4) := by decide
theorem ri_at_20 : fetchRel jsonReadItemCode 0x20 = some (.load .lbu a0 (20 : Fin 32) 0x0, 4) := by decide
theorem ri_at_24 : fetchRel jsonReadItemCode 0x24 = some (.aluImm .add a1 a0 0xFFFFFFDE, 4) := by decide
theorem ri_at_28 : fetchRel jsonReadItemCode 0x28 = some (.branch .beq a1 x0 0x12A, 4) := by decide
theorem ri_at_2c : fetchRel jsonReadItemCode 0x2C = some (.aluImm .add a1 a0 0xFFFFFFA5, 4) := by decide
theorem ri_at_30 : fetchRel jsonReadItemCode 0x30 = some (.branch .beq a1 x0 0x1A, 2) := by decide
theorem ri_at_32 : fetchRel jsonReadItemCode 0x32 = some (.aluImm .add a1 a0 0xFFFFFF9A, 4) := by decide
theorem ri_at_36 : fetchRel jsonReadItemCode 0x36 = some (.branch .beq a1 x0 0x72, 2) := by decide
theorem ri_at_38 : fetchRel jsonReadItemCode 0x38 = some (.aluImm .add a1 a0 0xFFFFFF92, 4) := by decide
theorem ri_at_3c : fetchRel jsonReadItemCode 0x3C = some (.branch .beq a1 x0 0x6C, 2) := by decide
theorem ri_at_3e : fetchRel jsonReadItemCode 0x3E = some (.aluImm .add a1 a0 0xFFFFFF8C, 4) := by decide
theorem ri_at_42 : fetchRel jsonReadItemCode 0x42 = some (.branch .beq a1 x0 0x66, 2) := by decide
theorem ri_at_44 : fetchRel jsonReadItemCode 0x44 = some (.aluImm .add a1 a0 0xFFFFFF85, 4) := by decide
theorem ri_at_48 : fetchRel jsonReadItemCode 0x48 = some (.branch .bne a1 x0 0x72, 2) := by decide
theorem ri_at_4a : fetchRel jsonReadItemCode 0x4A = some (.aluImm .add (21 : Fin 32) x0 0x0, 2) := by decide
theorem ri_at_4c : fetchRel jsonReadItemCode 0x4C = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem ri_at_4e : fetchRel jsonReadItemCode 0x4E = some (.branch .bgeu a3 (9 : Fin 32) 0x88, 4) := by decide
theorem ri_at_52 : fetchRel jsonReadItemCode 0x52 = some (.alu .add a0 (8 : Fin 32) a3, 4) := by decide
theorem ri_at_56 : fetchRel jsonReadItemCode 0x56 = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem ri_at_5a : fetchRel jsonReadItemCode 0x5A = some (.aluImm .add a1 a0 0xFFFFFFDE, 4) := by decide
theorem ri_at_5e : fetchRel jsonReadItemCode 0x5E = some (.branch .bne a1 x0 0x1C, 2) := by decide
theorem ri_at_60 : fetchRel jsonReadItemCode 0x60 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem ri_at_62 : fetchRel jsonReadItemCode 0x62 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem ri_at_64 : fetchRel jsonReadItemCode 0x64 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem ri_at_66 : fetchRel jsonReadItemCode 0x66 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem ri_at_68 : fetchRel jsonReadItemCode 0x68 = some (.auipc ra 0x0, 4) := by decide
theorem ri_at_6c : fetchRel jsonReadItemCode 0x6C = some (.jalr ra ra 0xFFFFFEA4, 4) := by decide
theorem ri_at_70 : fetchRel jsonReadItemCode 0x70 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem ri_at_74 : fetchRel jsonReadItemCode 0x74 = some (.branch .bne a0 x0 0xF2, 2) := by decide
theorem ri_at_76 : fetchRel jsonReadItemCode 0x76 = some (.load .lw a3 sp 0x10, 2) := by decide
theorem ri_at_78 : fetchRel jsonReadItemCode 0x78 = some (.jal x0 0xFFFFFFD6, 2) := by decide
theorem ri_at_7a : fetchRel jsonReadItemCode 0x7A = some (.aluImm .add a1 a0 0xFFFFFFA5, 4) := by decide
theorem ri_at_7e : fetchRel jsonReadItemCode 0x7E = some (.aluImm .add a3 a3 0x1, 2) := by decide
theorem ri_at_80 : fetchRel jsonReadItemCode 0x80 = some (.branch .beq a1 x0 0x20, 2) := by decide
theorem ri_at_82 : fetchRel jsonReadItemCode 0x82 = some (.aluImm .add a1 a0 0xFFFFFFA3, 4) := by decide
theorem ri_at_86 : fetchRel jsonReadItemCode 0x86 = some (.branch .beq a1 x0 0xE, 2) := by decide
theorem ri_at_88 : fetchRel jsonReadItemCode 0x88 = some (.aluImm .add a1 a0 0xFFFFFF85, 4) := by decide
theorem ri_at_8c : fetchRel jsonReadItemCode 0x8C = some (.branch .beq a1 x0 0x14, 2) := by decide
theorem ri_at_8e : fetchRel jsonReadItemCode 0x8E = some (.aluImm .add a0 a0 0xFFFFFF83, 4) := by decide
theorem ri_at_92 : fetchRel jsonReadItemCode 0x92 = some (.branch .bne a0 x0 0xFFFFFFBC, 2) := by decide
theorem ri_at_94 : fetchRel jsonReadItemCode 0x94 = some (.branch .beq (21 : Fin 32) x0 0x42, 4) := by decide
theorem ri_at_98 : fetchRel jsonReadItemCode 0x98 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem ri_at_9a : fetchRel jsonReadItemCode 0x9A = some (.branch .bne (21 : Fin 32) x0 0xFFFFFFB4, 4) := by decide
theorem ri_at_9e : fetchRel jsonReadItemCode 0x9E = some (.jal x0 0xD8, 2) := by decide
theorem ri_at_a0 : fetchRel jsonReadItemCode 0xA0 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x1, 2) := by decide
theorem ri_at_a2 : fetchRel jsonReadItemCode 0xA2 = some (.branch .beq (21 : Fin 32) x0 0x34, 4) := by decide
theorem ri_at_a6 : fetchRel jsonReadItemCode 0xA6 = some (.jal x0 0xFFFFFFA8, 2) := by decide
theorem ri_at_a8 : fetchRel jsonReadItemCode 0xA8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ri_at_aa : fetchRel jsonReadItemCode 0xAA = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem ri_at_ac : fetchRel jsonReadItemCode 0xAC = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem ri_at_ae : fetchRel jsonReadItemCode 0xAE = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem ri_at_b0 : fetchRel jsonReadItemCode 0xB0 = some (.auipc ra 0x0, 4) := by decide
theorem ri_at_b4 : fetchRel jsonReadItemCode 0xB4 = some (.jalr ra ra 0xCE, 4) := by decide
theorem ri_at_b8 : fetchRel jsonReadItemCode 0xB8 = some (.jal x0 0x26, 2) := by decide
theorem ri_at_ba : fetchRel jsonReadItemCode 0xBA = some (.aluImm .add a0 a0 0xFFFFFFD0, 4) := by decide
theorem ri_at_be : fetchRel jsonReadItemCode 0xBE = some (.aluImm .add a1 x0 0xA, 2) := by decide
theorem ri_at_c0 : fetchRel jsonReadItemCode 0xC0 = some (.branch .bgeu a0 a1 0x16, 4) := by decide
theorem ri_at_c4 : fetchRel jsonReadItemCode 0xC4 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ri_at_c6 : fetchRel jsonReadItemCode 0xC6 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem ri_at_c8 : fetchRel jsonReadItemCode 0xC8 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem ri_at_ca : fetchRel jsonReadItemCode 0xCA = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem ri_at_cc : fetchRel jsonReadItemCode 0xCC = some (.auipc ra 0x0, 4) := by decide
theorem ri_at_d0 : fetchRel jsonReadItemCode 0xD0 = some (.jalr ra ra 0x14E, 4) := by decide
theorem ri_at_d4 : fetchRel jsonReadItemCode 0xD4 = some (.jal x0 0xA, 2) := by decide
theorem ri_at_d6 : fetchRel jsonReadItemCode 0xD6 = some (.lui a0 0x2000, 2) := by decide
theorem ri_at_d8 : fetchRel jsonReadItemCode 0xD8 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem ri_at_da : fetchRel jsonReadItemCode 0xDA = some (.store .sh sp a0 0x4, 4) := by decide
theorem ri_at_de : fetchRel jsonReadItemCode 0xDE = some (.load .lbu a0 sp 0x4, 4) := by decide
theorem ri_at_e2 : fetchRel jsonReadItemCode 0xE2 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem ri_at_e4 : fetchRel jsonReadItemCode 0xE4 = some (.load .lbu a0 sp 0x5, 4) := by decide
theorem ri_at_e8 : fetchRel jsonReadItemCode 0xE8 = some (.jal x0 0x50, 2) := by decide
theorem ri_at_ea : fetchRel jsonReadItemCode 0xEA = some (.load .lw a2 sp 0x8, 2) := by decide
theorem ri_at_ec : fetchRel jsonReadItemCode 0xEC = some (.branch .bltu a2 (19 : Fin 32) 0x48, 4) := by decide
theorem ri_at_f0 : fetchRel jsonReadItemCode 0xF0 = some (.branch .bltu (9 : Fin 32) a2 0x44, 4) := by decide
theorem ri_at_f4 : fetchRel jsonReadItemCode 0xF4 = some (.alu .sub (19 : Fin 32) a2 (19 : Fin 32), 4) := by decide
theorem ri_at_f8 : fetchRel jsonReadItemCode 0xF8 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem ri_at_fa : fetchRel jsonReadItemCode 0xFA = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem ri_at_fc : fetchRel jsonReadItemCode 0xFC = some (.auipc ra 0x0, 4) := by decide
theorem ri_at_100 : fetchRel jsonReadItemCode 0x100 = some (.jalr ra ra 0x18C, 4) := by decide
theorem ri_at_104 : fetchRel jsonReadItemCode 0x104 = some (.branch .bgeu a0 (9 : Fin 32) 0x22, 4) := by decide
theorem ri_at_108 : fetchRel jsonReadItemCode 0x108 = some (.alu .add a1 (8 : Fin 32) a0, 4) := by decide
theorem ri_at_10c : fetchRel jsonReadItemCode 0x10C = some (.load .lbu a1 a1 0x0, 4) := by decide
theorem ri_at_110 : fetchRel jsonReadItemCode 0x110 = some (.aluImm .add a1 a1 0xFFFFFFD4, 4) := by decide
theorem ri_at_114 : fetchRel jsonReadItemCode 0x114 = some (.branch .bne a1 x0 0x12, 2) := by decide
theorem ri_at_116 : fetchRel jsonReadItemCode 0x116 = some (.aluImm .add a2 a0 0x1, 4) := by decide
theorem ri_at_11a : fetchRel jsonReadItemCode 0x11A = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem ri_at_11c : fetchRel jsonReadItemCode 0x11C = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem ri_at_11e : fetchRel jsonReadItemCode 0x11E = some (.auipc ra 0x0, 4) := by decide
theorem ri_at_122 : fetchRel jsonReadItemCode 0x122 = some (.jalr ra ra 0x16A, 4) := by decide
theorem ri_at_126 : fetchRel jsonReadItemCode 0x126 = some (.store .sw (18 : Fin 32) (20 : Fin 32) 0x0, 4) := by decide
theorem ri_at_12a : fetchRel jsonReadItemCode 0x12A = some (.store .sw (18 : Fin 32) (19 : Fin 32) 0x4, 4) := by decide
theorem ri_at_12e : fetchRel jsonReadItemCode 0x12E = some (.store .sw (18 : Fin 32) a0 0x8, 4) := by decide
theorem ri_at_132 : fetchRel jsonReadItemCode 0x132 = some (.jal x0 0xE, 2) := by decide
theorem ri_at_134 : fetchRel jsonReadItemCode 0x134 = some (.aluImm .add a0 x0 0x20, 4) := by decide
theorem ri_at_138 : fetchRel jsonReadItemCode 0x138 = some (.store .sw (18 : Fin 32) x0 0x0, 4) := by decide
theorem ri_at_13c : fetchRel jsonReadItemCode 0x13C = some (.store .sb (18 : Fin 32) a0 0x4, 4) := by decide
theorem ri_at_140 : fetchRel jsonReadItemCode 0x140 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem ri_at_142 : fetchRel jsonReadItemCode 0x142 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem ri_at_144 : fetchRel jsonReadItemCode 0x144 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem ri_at_146 : fetchRel jsonReadItemCode 0x146 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem ri_at_148 : fetchRel jsonReadItemCode 0x148 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem ri_at_14a : fetchRel jsonReadItemCode 0x14A = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem ri_at_14c : fetchRel jsonReadItemCode 0x14C = some (.load .lw (21 : Fin 32) sp 0x14, 2) := by decide
theorem ri_at_14e : fetchRel jsonReadItemCode 0x14E = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem ri_at_150 : fetchRel jsonReadItemCode 0x150 = some (.jalr x0 ra 0x0, 2) := by decide
theorem ri_at_152 : fetchRel jsonReadItemCode 0x152 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ri_at_154 : fetchRel jsonReadItemCode 0x154 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem ri_at_156 : fetchRel jsonReadItemCode 0x156 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem ri_at_158 : fetchRel jsonReadItemCode 0x158 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem ri_at_15a : fetchRel jsonReadItemCode 0x15A = some (.alu .add a3 x0 (19 : Fin 32), 2) := by decide
theorem ri_at_15c : fetchRel jsonReadItemCode 0x15C = some (.auipc ra 0x0, 4) := by decide
theorem ri_at_160 : fetchRel jsonReadItemCode 0x160 = some (.jalr ra ra 0xFFFFFDB0, 4) := by decide
theorem ri_at_164 : fetchRel jsonReadItemCode 0x164 = some (.jal x0 0xFFFFFF7A, 2) := by decide
theorem ri_at_166 : fetchRel jsonReadItemCode 0x166 = some (.load .lbu a0 sp 0xD, 4) := by decide
theorem ri_at_16a : fetchRel jsonReadItemCode 0x16A = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem ri_at_16c : fetchRel jsonReadItemCode 0x16C = some (.store .sb sp a1 0x4, 4) := by decide
theorem ri_at_170 : fetchRel jsonReadItemCode 0x170 = some (.store .sb sp a0 0x5, 4) := by decide
theorem ri_at_174 : fetchRel jsonReadItemCode 0x174 = some (.jal x0 0xFFFFFF6A, 2) := by decide
theorem ri_at_176 : fetchRel jsonReadItemCode 0x176 = some (.store .sb sp x0 0x4, 4) := by decide
theorem ri_at_17a : fetchRel jsonReadItemCode 0x17A = some (.store .sw sp a3 0x8, 2) := by decide
theorem ri_at_17c : fetchRel jsonReadItemCode 0x17C = some (.jal x0 0xFFFFFF62, 2) := by decide

theorem ri_q : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFDE) 0 = (b.toNat == 34) := by decide
theorem ri_q' : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFDE) 0 = !(b.toNat == 34) := by decide
theorem ri_lb : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFA5) 0 = (b.toNat == 91) := by decide
theorem ri_rb : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFA3) 0 = (b.toNat == 93) := by decide
theorem ri_lc : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF85) 0 = (b.toNat == 123) := by decide
theorem ri_lc' : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFF85) 0 = !(b.toNat == 123) := by decide
theorem ri_rc' : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFF83) 0 = !(b.toNat == 125) := by decide
theorem ri_f : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF9A) 0 = (b.toNat == 102) := by decide
theorem ri_n : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF92) 0 = (b.toNat == 110) := by decide
theorem ri_t : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF8C) 0 = (b.toNat == 116) := by decide
theorem ri_dg : ∀ b : BitVec 8,
    branchTaken .bgeu (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 0xA = !isDigit b.toNat := by decide
theorem ri_cm' : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFD4) 0 = !(b.toNat == 44) := by decide

theorem ri_inc (j : Nat) : aluEval .add (BitVec.ofNat 32 j) 1 = BitVec.ofNat 32 (j + 1) := ofNat_add_ofNat j 1

/-- `a` holds `r` as a `Result<usize, TufError>` whose error byte is `0x20`. -/
def ResAt (M : Word → BitVec 8) (a : Word) : Option Nat → Prop
  | some e => M a = 0 ∧ memLoad32 M (a + 4) = BitVec.ofNat 32 e
  | none => M a ≠ 0 ∧ M (a + 1) = 0x20

theorem UsizeRes.resAt {M M' : Word → BitVec 8} {a : Word} {r : Option Nat} (h : UsizeRes M M' a r) :
    ResAt M' a r := by
  cases r with
  | none => exact ⟨by rw [h.2.1]; decide, h.2.2⟩
  | some e => exact ⟨h.2.1, h.2.2⟩

/-- The cursor result of `read_item`: the value's slice and the position
after it. -/
def itemRes (p : Word) (pos : Nat) (r : Option (Nat × Nat)) : Option (Word × Nat × Nat) :=
  r.map fun x => (p + BitVec.ofNat 32 pos, x.1 - pos, x.2)

theorem curRes_err' (M : Word → BitVec 8) (out : Word) (e : BitVec 8) :
    CurRes M (memStore8 (memStore32 M out 0) (out + 4) e) out e none := by
  have s40 : Sep (out + BitVec.ofNat 32 4) 1 (out + BitVec.ofNat 32 0) 4 :=
    sep_offsets out (Or.inr (by decide)) (by decide) (by decide)
  rw [add_ofNat_zero] at s40
  refine ⟨fun x hx => ?_, (memLoad32_store8_sep s40).trans (memLoad32_store32_same _ _ _), memStore8_same _ _ _⟩
  have h0 : Sep x 1 out 4 := by have := sep_in hx (d := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  exact (out_store8 _ (out + BitVec.ofNat 32 4) _ x (sep_in hx (by decide))).trans (out_store32 _ _ _ x h0)

theorem curRes_ok' (M : Word → BitVec 8) (out q : Word) (l k : Nat) (e : BitVec 8) :
    CurRes M (memStore32 (memStore32 (memStore32 M out q) (out + 4) (BitVec.ofNat 32 l)) (out + 8)
      (BitVec.ofNat 32 k)) out e (some (q, l, k)) := by
  have s04 : Sep (out + BitVec.ofNat 32 0) 4 (out + BitVec.ofNat 32 4) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  have s08 : Sep (out + BitVec.ofNat 32 0) 4 (out + BitVec.ofNat 32 8) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  have s48 : Sep (out + BitVec.ofNat 32 4) 4 (out + BitVec.ofNat 32 8) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  rw [add_ofNat_zero] at s04 s08
  refine ⟨fun x hx => ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩
  · have h0 : Sep x 1 out 4 := by have := sep_in hx (d := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    exact ((out_store32 _ (out + BitVec.ofNat 32 8) _ x (sep_in hx (by decide))).trans
      (out_store32 _ (out + BitVec.ofNat 32 4) _ x (sep_in hx (by decide)))).trans (out_store32 _ _ _ x h0)
  · exact (memLoad32_store32_sep s08.symm).trans ((memLoad32_store32_sep s04.symm).trans
      (memLoad32_store32_same _ _ _))
  · exact (memLoad32_store32_sep s48.symm).trans (memLoad32_store32_same _ _ _)

/-- The registers `read_item` changes before its epilogue restores the saved ones. -/
abbrev riE : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21]

/-- The frame offsets of the saved registers. -/
abbrev riCs : List Nat := [0x14, 0x18, 0x1C, 0x20, 0x24, 0x28, 0x2C]

/-- The saved registers in the frame at `F`. -/
def RiSaved (F : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (F + BitVec.ofNat 32 0x2C) = g0 ra ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x28) = g0 8 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x24) = g0 9 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x20) = g0 18 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x1C) = g0 19 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x18) = g0 20 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x14) = g0 21

/-- Memory after the prologue. -/
def riM1 (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
    (F + 0x2C) (g0 ra)) (F + 0x28) (g0 8)) (F + 0x24) (g0 9)) (F + 0x20) (g0 18)) (F + 0x1C) (g0 19))
    (F + 0x18) (g0 20)) (F + 0x14) (g0 21)

theorem ri_pro (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) :
    Out M (riM1 M F g0) F 48 ∧ RiSaved F g0 (riM1 M F g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((((((out_store32 _ _ _).widen (d := 0x2C) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x28) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x24) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x20) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x1C) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x18) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x14) (by decide)))
  · exact ld_skip 0x2C 0x14 (by decide) (by decide) (by decide) (ld_skip 0x2C 0x18 (by decide) (by decide)
      (by decide) (ld_skip 0x2C 0x1C (by decide) (by decide) (by decide) (ld_skip 0x2C 0x20 (by decide)
      (by decide) (by decide) (ld_skip 0x2C 0x24 (by decide) (by decide) (by decide) (ld_skip 0x2C 0x28
      (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _))))))
  · exact ld_skip 0x28 0x14 (by decide) (by decide) (by decide) (ld_skip 0x28 0x18 (by decide) (by decide)
      (by decide) (ld_skip 0x28 0x1C (by decide) (by decide) (by decide) (ld_skip 0x28 0x20 (by decide)
      (by decide) (by decide) (ld_skip 0x28 0x24 (by decide) (by decide) (by decide)
      (memLoad32_store32_same _ _ _)))))
  · exact ld_skip 0x24 0x14 (by decide) (by decide) (by decide) (ld_skip 0x24 0x18 (by decide) (by decide)
      (by decide) (ld_skip 0x24 0x1C (by decide) (by decide) (by decide) (ld_skip 0x24 0x20 (by decide)
      (by decide) (by decide) (memLoad32_store32_same _ _ _))))
  · exact ld_skip 0x20 0x14 (by decide) (by decide) (by decide) (ld_skip 0x20 0x18 (by decide) (by decide)
      (by decide) (ld_skip 0x20 0x1C (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))
  · exact ld_skip 0x1C 0x14 (by decide) (by decide) (by decide) (ld_skip 0x1C 0x18 (by decide) (by decide)
      (by decide) (memLoad32_store32_same _ _ _))
  · exact ld_skip 0x18 0x14 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)
  · exact memLoad32_store32_same _ _ _

/-- The function returned to `ret` with `r` at `out`, changed only the 116
bytes at `s` besides, and kept every register outside `jClob`. -/
abbrev RiPost (ret : Word) (M : Word → BitVec 8) (out s : Word) (r : Option (Word × Nat × Nat))
    (g0 : Fin 32 → Word) : Post :=
  RPost ret (fun M' => CurResF M M' out s 116 0x20 r) g0

theorem Out.upK {M M' : Word → BitVec 8} {s F : Word} {c l k : Nat} (hF : s + BitVec.ofNat 32 c = F)
    (h : Out M M' F l) (hl : c + l ≤ k) : Out M M' s k := by
  subst hF; exact h.widen hl

theorem Out.mono {M M' : Word → BitVec 8} {s : Word} {l k : Nat} (h : Out M M' s l) (hl : l ≤ k) :
    Out M M' s k := Out.widen (d := 0) (by rw [add_ofNat_zero]; exact h) (by omega)

theorem riSepF {s F a : Word} {l c w : Nat} (hF : s + BitVec.ofNat 32 68 = F) (h : Sep s 116 a l)
    (hc : 68 + c + w ≤ 116) : Sep (F + BitVec.ofNat 32 c) w a l := by
  subst hF; rw [add_ofNat_assoc]; exact h.sub hc

theorem riSepFR {s F a : Word} {l c w : Nat} (hF : s + BitVec.ofNat 32 68 = F) (h : Sep a l s 116)
    (hc : 68 + c + w ≤ 116) : Sep a l (F + BitVec.ofNat 32 c) w := (riSepF hF h.symm hc).symm

/-- A word in the frame is apart from the 68 bytes below it. -/
theorem sep_below68 {s F : Word} (hF : s + BitVec.ofNat 32 68 = F) {c w : Nat} (hc : 68 + c + w ≤ 2 ^ 32) :
    Sep s 68 (F + BitVec.ofNat 32 c) w := by
  subst hF
  have := sep_offsets s (c := 0) (n := 68) (d := 68 + c) (k := w) (Or.inl (by omega)) (by omega) (by omega)
  rwa [add_ofNat_zero, ← add_ofNat_assoc] at this

section
variable {M M1 Mp : Word → BitVec 8} {base out s F p : Word} {f g0 : Fin 32 → Word}

theorem ri_epi {Mf : Word → BitVec 8} {R : (Word → BitVec 8) → Prop} (hsp : f sp = F)
    (hS : Slots riCs F M1 Mf) (hv : RiSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ riE → f x = g0 x) (hR : R Mf) :
    WP jsonReadItemCode base (RPost (g0 ra) R g0) Mf 0x140 f := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := hv
  have e1 : memLoad32 Mf (F + 0x2C) = g0 ra := (hS 0x2C (by decide)).trans v1
  have e2 : memLoad32 Mf (F + 0x28) = g0 8 := (hS 0x28 (by decide)).trans v2
  have e3 : memLoad32 Mf (F + 0x24) = g0 9 := (hS 0x24 (by decide)).trans v3
  have e4 : memLoad32 Mf (F + 0x20) = g0 18 := (hS 0x20 (by decide)).trans v4
  have e5 : memLoad32 Mf (F + 0x1C) = g0 19 := (hS 0x1C (by decide)).trans v5
  have e6 : memLoad32 Mf (F + 0x18) = g0 20 := (hS 0x18 (by decide)).trans v6
  have e7 : memLoad32 Mf (F + 0x14) = g0 21 := (hS 0x14 (by decide)).trans v7
  refine WP.lw ri_at_140 (by rw [hsp]; exact aligned_add hal (k := 0x2C) (by decide)) ?_; wn
  refine WP.lw ri_at_142 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x28) (by decide)) ?_; wn
  refine WP.lw ri_at_144 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x24) (by decide)) ?_; wn
  refine WP.lw ri_at_146 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x20) (by decide)) ?_; wn
  refine WP.lw ri_at_148 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x1C) (by decide)) ?_; wn
  refine WP.lw ri_at_14a (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x18) (by decide)) ?_; wn
  refine WP.lw ri_at_14c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x14) (by decide)) ?_; wn
  refine WP.aluImm ri_at_14e ?_; wn
  refine WP.ret ri_at_150 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18, 19, 20, 21]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]
  · rw [hsp, e5]
  · rw [hsp, e6]
  · rw [hsp, e7]

theorem ri_err {M2 : Word → BitVec 8} (h18 : f 18 = out) (hsp : f sp = F) (ha0 : (f a0).extractLsb' 0 8 = 0x20)
    (hF : s + BitVec.ofNat 32 68 = F) (hO : Out M M2 s 116) (hS : Slots riCs F Mp M2) (hv : RiSaved F g0 Mp)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ riE → f x = g0 x)
    (hso : Sep out 12 s 116) (hsc : Sep out 12 base jsonReadItemCode.length) :
    WP jsonReadItemCode base (RiPost (g0 ra) M out s none g0) M2 0x138 f := by
  refine WP.zero fun hz => ?_
  refine WP.sw ri_at_138 (by rw [h18]; exact aligned_add halo (k := 0) (by decide))
    (by rw [h18]; exact hsc.sub (c := 0) (by decide)) ?_; wn
  refine WP.sb ri_at_13c (by rw [h18]; exact hsc.sub (c := 4) (by decide)) ?_; wn
  rw [h18, add_lit_zero, ha0, hz]
  have hsoF : Sep out 12 F 48 := by rw [← hF]; exact hso.subR (c := 68) (l := 48) (by decide)
  refine ri_epi hsp (hS.out (curRes_err' M2 out 0x20).out (slots_sep_out hsoF (by decide))) hv hsp0 hret hal hz0
    hfr ⟨M2, hO, curRes_err' M2 out 0x20⟩

theorem ri_ok {M2 : Word → BitVec 8} {q : Word} {l k : Nat} (h18 : f 18 = out) (h20 : f 20 = q)
    (h19 : f 19 = BitVec.ofNat 32 l) (ha0 : f a0 = BitVec.ofNat 32 k) (hsp : f sp = F)
    (hF : s + BitVec.ofNat 32 68 = F) (hO : Out M M2 s 116) (hS : Slots riCs F Mp M2) (hv : RiSaved F g0 Mp)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ riE → f x = g0 x)
    (hso : Sep out 12 s 116) (hsc : Sep out 12 base jsonReadItemCode.length) :
    WP jsonReadItemCode base (RiPost (g0 ra) M out s (some (q, l, k)) g0) M2 0x126 f := by
  refine WP.sw ri_at_126 (by rw [h18]; exact aligned_add halo (k := 0) (by decide))
    (by rw [h18]; exact hsc.sub (c := 0) (by decide)) ?_; wn
  refine WP.sw ri_at_12a (by rw [h18]; exact aligned_add halo (k := 4) (by decide))
    (by rw [h18]; exact hsc.sub (c := 4) (by decide)) ?_; wn
  refine WP.sw ri_at_12e (by rw [h18]; exact aligned_add halo (k := 8) (by decide))
    (by rw [h18]; exact hsc.sub (c := 8) (by decide)) ?_; wn
  refine WP.jal ri_at_132 (by decide) ?_; wn
  rw [h18, add_lit_zero, h20, h19, ha0]
  have hsoF : Sep out 12 F 48 := by rw [← hF]; exact hso.subR (c := 68) (l := 48) (by decide)
  exact ri_epi hsp (hS.out (curRes_ok' M2 out q l k 0x20).out (slots_sep_out hsoF (by decide))) hv hsp0 hret hal
    hz0 hfr ⟨M2, hO, curRes_ok' M2 out q l k 0x20⟩

end

theorem ri_z : ∀ b : BitVec 8, branchTaken .beq (b.zeroExtend 32) 0 = decide (b = 0) := by decide

theorem ri_ze : ∀ b : BitVec 8, (b.zeroExtend 32).extractLsb' 0 8 = b := by decide

theorem itemTail_no {d : Bytes} {e : Nat} (h : ¬(skipWs d e < d.length ∧ d.getD (skipWs d e) 0 = 44)) :
    itemTail d e = (e, skipWs d e) := ite_eq_right_of_eq_false _ _ (eq_false h)

theorem itemTail_yes {d : Bytes} {e : Nat} (h : skipWs d e < d.length ∧ d.getD (skipWs d e) 0 = 44) :
    itemTail d e = (e, skipWs d (skipWs d e + 1)) := ite_eq_left_of_eq_true _ _ (eq_true h)

section
variable {M Mp : Word → BitVec 8} {base out s F p : Word} {f g0 : Fin 32 → Word}

theorem ri_tail {M2 : Word → BitVec 8} {r : Option Nat} {n pos : Nat}
    (h8 : f 8 = p) (h9 : f 9 = BitVec.ofNat 32 n) (h18 : f 18 = out)
    (h19 : f 19 = BitVec.ofNat 32 pos) (h20 : f 20 = p + BitVec.ofNat 32 pos) (hsp : f sp = F)
    (hF : s + BitVec.ofNat 32 68 = F) (hn : n < 2 ^ 32) (hbd : ∀ e, r = some e → pos < e ∧ e ≤ n)
    (hO : Out M M2 s 116) (hS : Slots riCs F Mp M2) (hv : RiSaved F g0 Mp) (hA : ResAt M2 (F + 4) r)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x30) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ riE → f x = g0 x) (hb : base.toNat % 2 = 0)
    (hcw : CodeIn M (base + 0x288) jsonSkipWsCode) (hSw : Sep s 116 (base + 0x288) jsonSkipWsCode.length)
    (hSp : Sep s 116 p n) (hso : Sep out 12 s 116) (hsc : Sep out 12 base jsonReadItemCode.length) :
    WP jsonReadItemCode base
      (RiPost (g0 ra) M out s (itemRes p pos (r.map (itemTail (memBytes M p n)))) g0) M2 0xDE f := by
  refine WP.zero fun hz => ?_
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  have hbm : memBytes M2 p n = memBytes M p n := hO.bytes hSp
  have hcw2 : CodeIn M2 (base + 0x288) jsonSkipWsCode := hO.codeIn hcw hSw
  refine WP.lbu ri_at_de ?_; wn
  rw [hsp]
  refine WP.branch ri_at_e2 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [ri_z] at e
    have e0 : M2 (F + 4) = 0 := of_decide_eq_true e
    rcases r with _ | ev
    · exact absurd e0 hA.1
    obtain ⟨hpe, hen⟩ := hbd ev rfl
    have he : memLoad32 M2 (F + 8) = BitVec.ofNat 32 ev := by
      rw [show F + 8 = F + 4 + 4 from by rw [BitVec.add_assoc]; rfl]; exact hA.2
    have hev : ev < 2 ^ 32 := by omega
    have hpos : pos < 2 ^ 32 := by omega
    refine WP.lw ri_at_ea (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 8) (by decide)) ?_; wn
    rw [hsp, he]
    refine WP.branch ri_at_ec (fun e => ?_) (fun _ => ?_) <;> wn
    · rsimp at e; rw [h19, br_bltu hev hpos] at e; exact absurd (of_decide_eq_true e) (by omega)
    refine WP.branch ri_at_f0 (fun e => ?_) (fun _ => ?_) <;> wn
    · rsimp at e; rw [h9, br_bltu hn hev] at e; exact absurd (of_decide_eq_true e) (by omega)
    refine WP.alu ri_at_f4 ?_; wn
    refine WP.alu ri_at_f8 ?_; wn
    refine WP.alu ri_at_fa ?_; wn
    refine WP.callSkipWs (tb := base + 0x288) (p := p) (n := n) (q := ev) ri_at_fc ri_at_100
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0x288 (by decide)) (by decide) hcw2
      (by (try rsimp); simp only [ev0, ev_mv hz, h8]) (by (try rsimp); simp only [ev0, ev_mv hz, h9])
      (by (try rsimp)) hn hev fun m2 r0 => ?_
    rw [hbm] at r0
    have hal' : skipWs (memBytes M p n) ev ≤ n := by have := skipWs_le (memBytes M p n) ev; omega
    have hs19 : aluEval .sub (BitVec.ofNat 32 ev) (f 19) = BitVec.ofNat 32 (ev - pos) := by
      rw [h19]; exact sub_ofNat_le (by omega) hev
    refine WP.branch ri_at_104 (fun e => ?_) (fun e => ?_) <;> wn
    · rsimp at e
      rw [r0, h9, br_bgeu (by omega) hn] at e
      have hge : ¬ skipWs (memBytes M p n) ev < n := not_dec_true e
      rw [Option.map_some, itemTail_no (by rw [hlen]; exact fun h => hge h.1)]
      exact ri_ok (by (try rsimp); exact h18) (by (try rsimp); exact h20) (by (try rsimp); exact hs19)
        (by (try rsimp); exact r0) (by (try rsimp); exact hsp) hF hO hS hv hsp0 hret hal halo hz0 (by keepz hz0)
        hso hsc
    rsimp at e
    rw [r0, h9, br_bgeu (by omega) hn] at e
    have hlt : skipWs (memBytes M p n) ev < n := not_dec_false e
    generalize hq : skipWs (memBytes M p n) ev = q at hlt r0
    have hq2 : q < 2 ^ 32 := by omega
    refine WP.alu ri_at_108 ?_; wn
    refine WP.lbu ri_at_10c ?_; wn
    refine WP.aluImm ri_at_110 ?_; wn
    have hbyte : M2 (p + BitVec.ofNat 32 q) = M (p + BitVec.ofNat 32 q) := hO.byte hSp hlt
    have hgd : (memBytes M p n).getD q 0 = (M (p + BitVec.ofNat 32 q)).toNat := memBytes_getD hlt
    refine WP.branch ri_at_114 (fun e => ?_) (fun e => ?_) <;> wn
    · rsimp at e
      rw [h8, r0, add_lit_zero, ri_cm', ev_add, hbyte] at e
      have hne : (M (p + BitVec.ofNat 32 q)).toNat ≠ 44 := nbeq_true e
      rw [Option.map_some, itemTail_no (by rw [hlen, hq, hgd]; exact fun h => hne h.2), hq]
      exact ri_ok (by (try rsimp); exact h18) (by (try rsimp); exact h20) (by (try rsimp); exact hs19)
        (by (try rsimp); exact r0) (by (try rsimp); exact hsp) hF hO hS hv hsp0 hret hal halo hz0 (by keepz hz0)
        hso hsc
    rsimp at e
    rw [h8, r0, add_lit_zero, ri_cm', ev_add, hbyte] at e
    have heq : (M (p + BitVec.ofNat 32 q)).toNat = 44 := nbeq_false e
    rw [Option.map_some, itemTail_yes (by rw [hlen, hq, hgd]; exact ⟨hlt, heq⟩), hq]
    refine WP.aluImm ri_at_116 ?_; wn
    refine WP.alu ri_at_11a ?_; wn
    refine WP.alu ri_at_11c ?_; wn
    refine WP.callSkipWs (tb := base + 0x288) (p := p) (n := n) (q := q + 1) ri_at_11e ri_at_122
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0x288 (by decide)) (by decide) hcw2
      (by (try rsimp); simp only [ev0, ev_mv hz, h8]) (by (try rsimp); simp only [ev0, ev_mv hz, h9])
      (by (try rsimp); rw [r0, ri_inc]) hn (by omega) fun m3 r1 => ?_
    rw [hbm] at r1
    exact ri_ok (by (try rsimp); exact h18) (by (try rsimp); exact h20) (by (try rsimp); exact hs19)
      (by (try rsimp); exact r1) (by (try rsimp); exact hsp) hF hO hS hv hsp0 hret hal halo hz0 (by keepz hz0)
      hso hsc
  · rsimp at e
    rw [ri_z] at e
    have e0 : M2 (F + 4) ≠ 0 := of_decide_eq_false e
    rcases r with _ | ev
    · refine WP.lbu ri_at_e4 ?_; wn
      refine WP.jal ri_at_e8 (by decide) ?_; wn
      have h5 : M2 (F + 5) = 0x20 := by
        rw [show F + 5 = F + 4 + 1 from by rw [BitVec.add_assoc]; rfl]; exact hA.2
      exact ri_err (by (try rsimp); exact h18) (by (try rsimp); exact hsp)
        (by (try rsimp); rw [hsp, h5]; rfl) hF hO hS hv hsp0 hret hal halo hz0 (by keepz hz0) hso hsc
    · exact absurd hA.1 e0

end

theorem ri_dec (j : Nat) : aluEval .add (BitVec.ofNat 32 (j + 1)) 0xFFFFFFFF = BitVec.ofNat 32 j := by
  rw [ev_add, ← ofNat_add_ofNat j 1, BitVec.add_assoc, show (BitVec.ofNat 32 1 : Word) + 0xFFFFFFFF = 0 from by decide]
  exact BitVec.add_zero _

theorem ri_nz : ∀ b : BitVec 8, branchTaken .bne (b.zeroExtend 32) 0 = !decide (b = 0) := by decide

theorem cScan_succ (d : Bytes) (k depth i : Nat) : cScan d (k + 1) depth i =
    if d.length ≤ i then none
    else if d.getD i 0 = 34 then (stringEnd true d i).bind (cScan d k depth)
    else if d.getD i 0 = 91 ∨ d.getD i 0 = 123 then cScan d k (depth + 1) (i + 1)
    else if d.getD i 0 = 93 ∨ d.getD i 0 = 125 then
      (if depth = 0 then none else if depth = 1 then some (i + 1) else cScan d k (depth - 1) (i + 1))
    else cScan d k depth (i + 1) := rfl

theorem resAt_some (M : Word → BitVec 8) (a : Word) (v : Nat) :
    ResAt (memStore32 (memStore8 M a 0) (a + 4) (BitVec.ofNat 32 v)) a (some v) := by
  have h4 : Sep (a + BitVec.ofNat 32 4) 4 (a + BitVec.ofNat 32 0) 1 :=
    sep_offsets a (Or.inr (by decide)) (by decide) (by decide)
  rw [add_ofNat_zero] at h4
  exact ⟨(memStore32_get_sep h4).trans (memStore8_same _ _ _), memLoad32_store32_same _ _ _⟩

theorem resAt_err (M : Word → BitVec 8) (a : Word) :
    ResAt (memStore8 (memStore8 M a 1) (a + 1) 0x20) a none := by
  refine ⟨?_, memStore8_same _ _ _⟩
  rw [memStore8_ne (Ne.symm (ne_add_one a)), memStore8_same]
  decide

/-- The registers the dispatch and the scan change before `0xDE`. -/
abbrev riLp : List (Fin 32) := [ra, 21, a0, a1, a2, a3, a4, a5, a6, a7, t0, t1]

/-- The rest of the function from `0xDE`, for every memory and registers
that hold `r` in the slot at `F + 4`. -/
def RiK (base : Word) (Q : Post) (M : Word → BitVec 8) (s F : Word) (Mp : Word → BitVec 8)
    (f0 : Fin 32 → Word) (r : Option Nat) : Prop :=
  ∀ M3 g, Out M M3 s 116 → Slots riCs F Mp M3 → ResAt M3 (F + 4) r → (∀ x, x ∉ riLp → g x = f0 x) →
    WP jsonReadItemCode base Q M3 0xDE g

section
variable {M Mp : Word → BitVec 8} {base s F p : Word} {f f0 : Fin 32 → Word} {Q : Post}

theorem ri_d6 {M2 : Word → BitVec 8} (hsp : f sp = F) (hf : ∀ x, x ∉ riLp → f x = f0 x)
    (hF : s + BitVec.ofNat 32 68 = F) (halF : F.toNat % 4 = 0) (hSc : Sep s 116 base jsonReadItemCode.length)
    (hO : Out M M2 s 116) (hS : Slots riCs F Mp M2) (hz0 : f0 0 = 0) (hK : RiK base Q M s F Mp f0 none) :
    WP jsonReadItemCode base Q M2 0xD6 f := by
  refine WP.lui ri_at_d6 ?_; wn
  refine WP.aluImm ri_at_d8 ?_; wn
  refine WP.sh ri_at_da (by
      (try rsimp); rw [hsp]
      exact (show (F + BitVec.ofNat 32 4).toNat % 2 = 0 by have := aligned_add halF (k := 4) (by decide); omega))
    (by (try rsimp); rw [hsp]; exact riSepF hF hSc (by decide)) ?_; wn
  (try rsimp)
  rw [hsp]
  have hU := usizeRes_err16 M2 (F + 4)
  exact hK _ _ (hO.trans (Out.upK (c := 72) (by rw [← hF, BitVec.add_assoc]; rfl) hU.out (by decide)))
    (hS.out hU.out (slots_sep F (d := 4) (l := 8) (by decide) (by decide))) hU.resAt (by keepz hz0)

end

section
variable {M Mp : Word → BitVec 8} {base s F p : Word} {f0 : Fin 32 → Word} {Q : Post}

theorem ri_loop {n : Nat} (hn : n < 2 ^ 32) (hF : s + BitVec.ofNat 32 68 = F) (hb : base.toNat % 2 = 0)
    (halF : F.toNat % 4 = 0) (hcse : CodeIn M (base + 0xFFFFFF0C) jsonStringEndCode)
    (hSse : Sep s 116 (base + 0xFFFFFF0C) jsonStringEndCode.length) (hSc : Sep s 116 base jsonReadItemCode.length)
    (hSp : Sep s 116 p n) (h8 : f0 8 = p) (h9 : f0 9 = BitVec.ofNat 32 n) (hsp : f0 sp = F) (hz0 : f0 0 = 0) :
    ∀ (k depth i : Nat) (M2 : Word → BitVec 8) (f : Fin 32 → Word), (∀ x, x ∉ riLp → f x = f0 x) →
      f 21 = BitVec.ofNat 32 depth → f a3 = BitVec.ofNat 32 i → n - i < k → depth ≤ i → i ≤ n →
      Out M M2 s 116 → Slots riCs F Mp M2 → RiK base Q M s F Mp f0 (cScan (memBytes M p n) k depth i) →
      WP jsonReadItemCode base Q M2 0x4E f := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ hk; exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
  intro depth i M2 f hf h21 ha3 hk hdi hin hO hS hK
  refine WP.zero fun hz => ?_
  have f8 : f 8 = p := (hf 8 (by decide)).trans h8
  have f9 : f 9 = BitVec.ofNat 32 n := (hf 9 (by decide)).trans h9
  have fsp : f sp = F := (hf sp (by decide)).trans hsp
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  have hi32 : i < 2 ^ 32 := by omega
  refine WP.branch ri_at_4e (fun e => ?_) (fun e => ?_) <;> wn
  · rw [ha3, f9, br_bgeu hi32 hn] at e
    have hge : ¬ i < n := not_dec_true e
    rw [cScan_succ, hlen, ite_eq_left_of_eq_true _ _ (eq_true (show n ≤ i by omega))] at hK
    exact ri_d6 fsp hf hF halF hSc hO hS hz0 hK
  rw [ha3, f9, br_bgeu hi32 hn] at e
  have hlt : i < n := not_dec_false e
  have hbyte : M2 (p + BitVec.ofNat 32 i) = M (p + BitVec.ofNat 32 i) := hO.byte hSp hlt
  have hgd : (memBytes M p n).getD i 0 = (M (p + BitVec.ofNat 32 i)).toNat := memBytes_getD hlt
  generalize hB : M (p + BitVec.ofNat 32 i) = B at hbyte hgd
  rw [cScan_succ, hlen, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ n ≤ i by omega)), hgd] at hK
  refine WP.alu ri_at_52 ?_; wn
  refine WP.lbu ri_at_56 ?_; wn
  rw [f8, ha3, ev_add, add_lit_zero, hbyte]
  refine WP.aluImm ri_at_5a ?_; wn
  have hopen : ∀ g : Fin 32 → Word, (∀ x, x ∉ riLp → g x = f0 x) → g 21 = BitVec.ofNat 32 depth →
      g a3 = BitVec.ofNat 32 (i + 1) → RiK base Q M s F Mp f0 (cScan (memBytes M p n) k (depth + 1) (i + 1)) →
      WP jsonReadItemCode base Q M2 0xA0 g := by
    intro g hg g21 ga3 hK'
    refine WP.zero fun hz' => ?_
    refine WP.aluImm ri_at_a0 ?_; wn
    refine WP.branch ri_at_a2 (fun e => ?_) (fun _ => ?_) <;> wn
    · (try rsimp at e); (try rw [hz'] at e); rw [g21, ri_inc, br_beq0 (by omega)] at e
      exact absurd (of_decide_eq_true e) (by omega)
    refine WP.jal ri_at_a6 (by decide) ?_; wn
    exact ih (depth + 1) (i + 1) M2 _ (by keepz hz0) (by (try rsimp); rw [g21, ri_inc]) (by (try rsimp); exact ga3)
      (by omega) (by omega) (by omega) hO hS hK'
  have hclose : ∀ g : Fin 32 → Word, (∀ x, x ∉ riLp → g x = f0 x) → g 21 = BitVec.ofNat 32 depth →
      g a3 = BitVec.ofNat 32 (i + 1) →
      RiK base Q M s F Mp f0 (if depth = 0 then none else if depth = 1 then some (i + 1)
        else cScan (memBytes M p n) k (depth - 1) (i + 1)) →
      WP jsonReadItemCode base Q M2 0x94 g := by
    intro g hg g21 ga3 hK'
    refine WP.zero fun hz' => ?_
    have gsp : g sp = F := (hg sp (by decide)).trans hsp
    refine WP.branch ri_at_94 (fun e => ?_) (fun e => ?_) <;> wn
    · (try rsimp at e); (try rw [hz'] at e); rw [g21, br_beq0 (by omega)] at e
      rw [ite_eq_left_of_eq_true _ _ (eq_true (of_decide_eq_true e))] at hK'
      exact ri_d6 gsp hg hF halF hSc hO hS hz0 hK'
    (try rsimp at e); (try rw [hz'] at e); rw [g21, br_beq0 (by omega)] at e
    have hd0 : depth ≠ 0 := of_decide_eq_false e
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd0)] at hK'
    obtain ⟨d', rfl⟩ : ∃ d', depth = d' + 1 := ⟨depth - 1, by omega⟩
    refine WP.aluImm ri_at_98 ?_; wn
    refine WP.branch ri_at_9a (fun e => ?_) (fun e => ?_) <;> wn
    · (try rsimp at e); (try rw [hz'] at e); rw [g21, ri_dec, br_bne0 (by omega)] at e
      have h1 : d' ≠ 0 := not_dec_true e
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ d' + 1 = 1 by omega)), Nat.add_sub_cancel] at hK'
      exact ih d' (i + 1) M2 _ (by keepz hz0) (by (try rsimp); rw [g21, ri_dec]) (by (try rsimp); exact ga3)
        (by omega) (by omega) (by omega) hO hS hK'
    (try rsimp at e); (try rw [hz'] at e); rw [g21, ri_dec, br_bne0 (by omega)] at e
    obtain rfl : d' = 0 := not_dec_false e
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at hK'
    refine WP.jal ri_at_9e (by decide) ?_; wn
    refine WP.sb ri_at_176 (by (try rsimp); rw [gsp]; exact riSepF hF hSc (by decide)) ?_; wn
    refine WP.sw ri_at_17a (by (try rsimp); rw [gsp]; exact aligned_add halF (k := 8) (by decide))
      (by (try rsimp); rw [gsp]; exact riSepF hF hSc (by decide)) ?_; wn
    refine WP.jal ri_at_17c (by decide) ?_; wn
    (try rsimp)
    rw [gsp]; (try rw [ga3]); (try rw [hz'])
    rw [show BitVec.extractLsb' 0 8 (0 : Word) = 0 from rfl,
      show F + 8 = F + 4 + 4 from by rw [BitVec.add_assoc]; rfl]
    have hO3 : Out M2 (memStore32 (memStore8 M2 (F + 4) 0) (F + 4 + 4) (BitVec.ofNat 32 (i + 1))) (F + 4) 8 :=
      ((out_store8 _ _ _).mono (by decide)).trans ((out_store32 _ _ _).widen (d := 4) (by decide))
    exact hK' _ _ (hO.trans (Out.upK (c := 72) (by rw [← hF, BitVec.add_assoc]; rfl) hO3 (by decide)))
      (hS.out hO3 (slots_sep F (d := 4) (l := 8) (by decide) (by decide))) (resAt_some _ _ _) (by keepz hz0)
  refine WP.branch ri_at_5e (fun e => ?_) (fun e => ?_) <;> wn
  · (try rsimp at e); (try rw [hz] at e); rw [ri_q'] at e
    have hq : B.toNat ≠ 34 := nbeq_true e
    rw [ite_eq_right_of_eq_false _ _ (eq_false hq)] at hK
    refine WP.aluImm ri_at_7a ?_; wn
    refine WP.aluImm ri_at_7e ?_; wn
    refine WP.branch ri_at_80 (fun e => ?_) (fun e => ?_) <;> wn
    · (try rsimp at e); (try rw [hz] at e); rw [ri_lb] at e
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl (beq_iff_eq.mp e)))] at hK
      exact hopen _ (by keepz hz0) (by (try rsimp); exact h21) (by (try rsimp); rw [ha3, ri_inc]) hK
    (try rsimp at e); (try rw [hz] at e); rw [ri_lb] at e
    have h91 : B.toNat ≠ 91 := fun h => by rw [h] at e; exact absurd e (by decide)
    refine WP.aluImm ri_at_82 ?_; wn
    refine WP.branch ri_at_86 (fun e => ?_) (fun e => ?_) <;> wn
    · (try rsimp at e); (try rw [hz] at e); rw [ri_rb] at e
      have h93 : B.toNat = 93 := beq_iff_eq.mp e
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (Or.inl h93))] at hK
      exact hclose _ (by keepz hz0) (by (try rsimp); exact h21) (by (try rsimp); rw [ha3, ri_inc]) hK
    (try rsimp at e); (try rw [hz] at e); rw [ri_rb] at e
    have h93 : B.toNat ≠ 93 := fun h => by rw [h] at e; exact absurd e (by decide)
    refine WP.aluImm ri_at_88 ?_; wn
    refine WP.branch ri_at_8c (fun e => ?_) (fun e => ?_) <;> wn
    · (try rsimp at e); (try rw [hz] at e); rw [ri_lc] at e
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (beq_iff_eq.mp e)))] at hK
      exact hopen _ (by keepz hz0) (by (try rsimp); exact h21) (by (try rsimp); rw [ha3, ri_inc]) hK
    (try rsimp at e); (try rw [hz] at e); rw [ri_lc] at e
    have h123 : B.toNat ≠ 123 := fun h => by rw [h] at e; exact absurd e (by decide)
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hK
    refine WP.aluImm ri_at_8e ?_; wn
    refine WP.branch ri_at_92 (fun e => ?_) (fun e => ?_) <;> wn
    · (try rsimp at e); (try rw [hz] at e); rw [ri_rc'] at e
      have h125 : B.toNat ≠ 125 := nbeq_true e
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at hK
      exact ih depth (i + 1) M2 _ (by keepz hz0) (by (try rsimp); exact h21) (by (try rsimp); rw [ha3, ri_inc])
        (by omega) (by omega) (by omega) hO hS hK
    (try rsimp at e); (try rw [hz] at e); rw [ri_rc'] at e
    have h125 : B.toNat = 125 := nbeq_false e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr h125))] at hK
    exact hclose _ (by keepz hz0) (by (try rsimp); exact h21) (by (try rsimp); rw [ha3, ri_inc]) hK
  (try rsimp at e); (try rw [hz] at e); rw [ri_q'] at e
  have hq : B.toNat = 34 := nbeq_false e
  rw [ite_eq_left_of_eq_true _ _ (eq_true hq)] at hK
  refine WP.aluImm ri_at_60 ?_; wn
  refine WP.aluImm ri_at_62 ?_; wn
  refine WP.alu ri_at_64 ?_; wn
  refine WP.alu ri_at_66 ?_; wn
  refine WP.callStringEnd (tb := base + 0xFFFFFF0C) (out := F + 0xC) (p := p) (n := n) (pos := i) (c := true)
    ri_at_68 ri_at_6c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0xFFFFFF0C (by decide))
    (by decide) (hO.codeIn hcse hSse) (by (try rsimp); rw [fsp, ev_add]) (by (try rsimp); simp only [ev0, ev_mv hz, f8])
    (by (try rsimp); simp only [ev0, ev_mv hz, f9]) (by (try rsimp); exact ha3)
    (by (try rsimp); (try simp only [ev0, ev_mv hz])) hn hi32 (aligned_add halF (k := 0xC) (by decide))
    (riSepF hF hSse (by decide)) (riSepF hF hSc (by decide)) fun m2 hU => ?_
  rw [hO.bytes hSp] at hU
  have hO2 : Out M m2.mem s 116 :=
    hO.trans (Out.upK (c := 80) (by rw [← hF, BitVec.add_assoc]; rfl) hU.out (by decide))
  have hS2 : Slots riCs F Mp m2.mem := hS.out hU.out (slots_sep F (d := 0xC) (l := 8) (by decide) (by decide))
  refine WP.lbu ri_at_70 ?_; wn
  rcases hse : stringEnd true (memBytes M p n) i with _ | j
  · rw [hse] at hU
    have hK' : RiK base Q M s F Mp f0 none := by rw [hse] at hK; exact hK
    refine WP.branch ri_at_74 (fun _ => ?_) (fun e => ?_) <;> wn
    · refine WP.lbu ri_at_166 ?_; wn
      refine WP.aluImm ri_at_16a ?_; wn
      refine WP.sb ri_at_16c (by (try rsimp); rw [fsp]; exact riSepF hF hSc (by decide)) ?_; wn
      refine WP.sb ri_at_170 (by (try rsimp); rw [fsp]; exact riSepF hF hSc (by decide)) ?_; wn
      refine WP.jal ri_at_174 (by decide) ?_; wn
      have h0d : m2.mem (F + 0xD) = 0x20 := by
        rw [show F + 0xD = F + 0xC + 1 from by rw [BitVec.add_assoc]; rfl]; exact hU.2.2
      (try rsimp)
      rw [fsp, h0d, ri_ze, show BitVec.extractLsb' 0 8 (aluEval .add (0 : Word) 1) = 1 from rfl,
        show F + 5 = F + 4 + 1 from by rw [BitVec.add_assoc]; rfl]
      have hO3 : Out m2.mem (memStore8 (memStore8 m2.mem (F + 4) 1) (F + 4 + 1) 0x20) (F + 4) 8 :=
        ((out_store8 _ _ _).mono (by decide)).trans
          ((out_store8 _ _ _).widen (d := 1) (by decide))
      exact hK' _ _ (hO2.trans (Out.upK (c := 72) (by rw [← hF, BitVec.add_assoc]; rfl) hO3 (by decide)))
        (hS2.out hO3 (slots_sep F (d := 4) (l := 8) (by decide) (by decide))) (resAt_err _ _) (by keepz hz0)
    · (try rsimp at e); (try rw [hz] at e); rw [fsp, hU.2.1] at e; exact absurd e (by decide)
  · rw [hse] at hU
    have hK' : RiK base Q M s F Mp f0 (cScan (memBytes M p n) k depth j) := by rw [hse] at hK; exact hK
    have hj1 := stringEnd_gt hse
    have hj2 := stringEnd_le hse
    rw [hlen] at hj2
    refine WP.branch ri_at_74 (fun e => ?_) (fun _ => ?_) <;> wn
    · (try rsimp at e); (try rw [hz] at e); rw [fsp, hU.2.1] at e; exact absurd e (by decide)
    refine WP.lw ri_at_76 (by (try rsimp); rw [fsp]; exact aligned_add halF (k := 0x10) (by decide)) ?_; wn
    refine WP.jal ri_at_78 (by decide) ?_; wn
    have hj : memLoad32 m2.mem (F + 0x10) = BitVec.ofNat 32 j := by
      rw [show F + 0x10 = F + 0xC + 4 from by rw [BitVec.add_assoc]; rfl]; exact hU.2.2
    exact ih depth j m2.mem _ (by keepz hz0) (by (try rsimp); exact h21) (by (try rsimp); rw [fsp, hj])
      (by omega) (by omega) hj2 hO2 hS2 hK'

end
