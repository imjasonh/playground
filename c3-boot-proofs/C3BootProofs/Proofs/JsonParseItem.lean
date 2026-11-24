import C3BootProofs.Proofs.JsonParseLoop

/-!
# `json::parse`: scalar values

The calls to `string_end`, `literal_end`, and `number_end` from `parse`'s
value loop, the check of their result at `0x11A`, and the entry to the
closing loop at `0x124`.
-/

namespace C3.RV32

open C3.Image C3.Json

theorem pi_ad_es (b : Word) : b + 0x17E + 0xFFFFF400 = b + 0xFFFFF57E := by
  rw [BitVec.add_assoc]; rfl

theorem pi_ad_mc (b : Word) : b + 0x17E + 0xC7BE = b + 0xC93C := by
  rw [BitVec.add_assoc]; rfl

section
variable {M0 Mp : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 f : Fin 32 → Word}

/-- The error exit at `0x2CC`. -/
theorem pa_2cc (E : PaEnv M0 base s p out n g0 Mp F) {M : Word → BitVec 8} (hsp : f sp = F) (h18 : f 18 = out)
    (hO : Out M0 M s 404) (hS : Slots paCs F Mp M) (hfr : ∀ x, x ∉ paE → f x = g0 x) :
    WP jsonParseCode base (PPost M0 s p out g0 (.error 0x20)) M 0x2CC f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm pa_at_2cc ?_; wn
  refine WP.jal pa_at_2d0 (by decide) ?_; wn
  exact pa_302 E (by (try rsimp); exact hsp) (by (try rsimp); exact h18)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); rfl) hO hS (by keepz E.z0)

/-- The closing loop's entry at `0x126`, after a value that ends at `e`. -/
theorem pa_126 (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {start e : Nat} {w27 : Word}
    {stk : List (Bool × Nat)} {M : Word → BitVec 8} {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hnext : PNext M0 Mp base s p out F n c g0 (BitVec.ofNat 32 start) w27 next) (hst : start ≤ n)
    (hFI : FInv M0 Mp s F n stk M) (hR : PRegs f g0 F p n c) (h18 : f 18 = out)
    (h25 : f 25 = BitVec.ofNat 32 e) (he : e ≤ n) (h8 : f 8 = BitVec.ofNat 32 stk.length)
    (h22 : f 22 = BitVec.ofNat 32 stk.length) (h26 : f 26 = BitVec.ofNat 32 start) (h27 : f 27 = w27) :
    WP jsonParseCode base (PPost M0 s p out g0 (afterClose (closeLoop c (memBytes M0 p n) start 17 stk e) next))
      M 0x126 f := by
  have hfr := hR.fr
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  refine WP.zero fun hz => ?_
  refine WP.sw pa_at_126 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xC) (by decide))
    (by (try rsimp); rw [hR.sp]; exact E.sepF E.sep.parse (d := 0xC) (w := 4) (by decide)) ?_; wn
  rw [hR.sp, h18]
  have hFI' : FInv M0 Mp s F n stk (memStore32 M (F + 0xC) out) :=
    hFI.outF E.hF (d := 0xC) (out_store32 _ _ _) (Or.inl (by decide))
  refine WP.aluImm pa_at_128 ?_; wn
  refine WP.alu pa_at_12a ?_; wn
  exact pa_close E hnext hst hFI.2.2.1 17 stk e _ _ (Nat.le_refl _) he hFI' (memLoad32_store32_same _ _ _)
    (by pregs hR, E.z0) (by (try rsimp); (try simp only [ev0, ev_mv hz]); rfl) (by (try rsimp); exact h25)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h22) (by (try rsimp); exact h22)
    (by (try rsimp); exact h26) (by (try rsimp); exact h27)

/-- The check at `0x11A` of the result that a scalar's end function left at
`F + 0xA8`. -/
theorem pa_res (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {start : Nat} {w27 : Word}
    {stk : List (Bool × Nat)} {Ma M : Word → BitVec 8} {r : Option Nat}
    {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hnext : PNext M0 Mp base s p out F n c g0 (BitVec.ofNat 32 start) w27 next) (hst : start ≤ n)
    (hU : UsizeRes Ma M (F + 0xA8) r) (hr : ∀ e, r = some e → e ≤ n)
    (hFI : FInv M0 Mp s F n stk M) (hR : PRegs f g0 F p n c) (h18 : f 18 = out)
    (h8 : f 8 = BitVec.ofNat 32 stk.length) (h26 : f 26 = BitVec.ofNat 32 start) (h27 : f 27 = w27) :
    WP jsonParseCode base (PPost M0 s p out g0 (match (generalizing := false) r with
      | none => .error 0x20
      | some e => afterClose (closeLoop c (memBytes M0 p n) start 17 stk e) next)) M 0x11A f := by
  have hfr := hR.fr
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  refine WP.zero fun hz => ?_
  refine WP.lbu pa_at_11a ?_; wn
  rcases r with _ | e
  · obtain ⟨-, t1, t2⟩ := hU
    have t2' : M (F + 0xA9) = 0x20 := by
      rw [show F + 0xA9 = F + 0xA8 + 1 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch pa_at_11e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
    refine WP.lbu pa_at_2fe ?_; wn
    exact pa_302 E (by (try rsimp); exact hR.sp) (by (try rsimp); exact h18)
      (by (try rsimp); rw [hR.sp, t2', ri_ze]; try rfl) hFI.1 hFI.2.1 (by keepz E.z0)
  obtain ⟨-, t1, t2⟩ := hU
  have t2' : memLoad32 M (F + 0xAC) = BitVec.ofNat 32 e := by
    rw [show F + 0xAC = F + 0xA8 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
  refine WP.branch pa_at_11e (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; (try rsimp at eb); rw [hR.sp, t1] at eb; exact absurd eb (by decide)
  refine WP.lw pa_at_122 (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xAC) (by decide)) ?_; wn
  refine WP.alu pa_at_124 ?_; wn
  exact pa_126 E hnext hst hFI (by pregs hR, E.z0) (by (try rsimp); exact h18)
    (by (try rsimp); rw [hR.sp, t2']) (hr e rfl) (by (try rsimp); exact h8)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h8) (by (try rsimp); exact h26)
    (by (try rsimp); exact h27)

theorem pa_FA8 (E : PaEnv M0 base s p out n g0 Mp F) : F + 0xA8 = s + BitVec.ofNat 32 332 := by
  rw [← E.hF, BitVec.add_assoc]; rfl

/-- A string value at `0x108`: the call to `string_end`. -/
theorem pa_str (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {start pos : Nat} {w27 : Word}
    {stk : List (Bool × Nat)} {M : Word → BitVec 8} {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hnext : PNext M0 Mp base s p out F n c g0 (BitVec.ofNat 32 start) w27 next) (hst : start ≤ n)
    (hFI : FInv M0 Mp s F n stk M) (hR : PRegs f g0 F p n c) (h18 : f 18 = out)
    (h25 : f 25 = BitVec.ofNat 32 pos) (hpos : pos ≤ n) (h8 : f 8 = BitVec.ofNat 32 stk.length)
    (h26 : f 26 = BitVec.ofNat 32 start) (h27 : f 27 = w27) :
    WP jsonParseCode base (PPost M0 s p out g0 (match stringEnd c (memBytes M0 p n) pos with
      | none => .error 0x20
      | some e => afterClose (closeLoop c (memBytes M0 p n) start 17 stk e) next)) M 0x108 f := by
  have hfr := hR.fr
  have hn := E.hn
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  have hd : memBytes M p n = memBytes M0 p n := hFI.1.bytes E.sP
  refine WP.zero fun hz => ?_
  refine WP.aluImm pa_at_108 ?_; wn
  refine WP.alu pa_at_10a ?_; wn
  refine WP.alu pa_at_10c ?_; wn
  refine WP.alu pa_at_10e ?_; wn
  refine WP.alu pa_at_110 ?_; wn
  refine WP.callStringEnd (tb := base + 0xFFFFF372 + 0xFFFFF616 + 0xFFFFFF0C) (out := F + 0xA8) (p := p)
    (n := n) (pos := pos) (c := c) pa_at_112 pa_at_116 (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) _ (by decide)) (by decide)
    hc1.get.ri.se (by (try rsimp); rw [hR.sp, ev_add])
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s7)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s8)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h25)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s3) (by omega) (by omega)
    (E.alF (d := 0xA8) (by decide)) (E.sepF E.sep.get.ri.se (d := 0xA8) (w := 8) (by decide))
    (E.sepF E.sep.parse (d := 0xA8) (w := 8) (by decide)) fun m2 hU => ?_
  rw [hd] at hU
  generalize m2.mem = M2 at hU
  have hFI2 : FInv M0 Mp s F n stk M2 := hFI.outF E.hF (d := 0xA8) hU.out (Or.inr ⟨by decide, by decide⟩)
  exact pa_res E hnext hst hU (fun e he => by have := stringEnd_le he; rwa [memBytes_length] at this) hFI2
    (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h8) (by (try rsimp); exact h26)
    (by (try rsimp); exact h27)

/-- A number at `0xF6`, after the check of its first digit: the call to
`number_end`. -/
theorem pa_num (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {start pos : Nat} {w27 : Word}
    {stk : List (Bool × Nat)} {M : Word → BitVec 8} {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hnext : PNext M0 Mp base s p out F n c g0 (BitVec.ofNat 32 start) w27 next) (hst : start ≤ n)
    (hFI : FInv M0 Mp s F n stk M) (hR : PRegs f g0 F p n c) (h18 : f 18 = out)
    (h25 : f 25 = BitVec.ofNat 32 pos) (hpos : pos ≤ n) (h8 : f 8 = BitVec.ofNat 32 stk.length)
    (h26 : f 26 = BitVec.ofNat 32 start) (h27 : f 27 = w27) :
    WP jsonParseCode base (PPost M0 s p out g0 (match numberEnd (memBytes M0 p n) pos with
      | none => .error 0x20
      | some e => afterClose (closeLoop c (memBytes M0 p n) start 17 stk e) next)) M 0xF6 f := by
  have hfr := hR.fr
  have hn := E.hn
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  have hd : memBytes M p n = memBytes M0 p n := hFI.1.bytes E.sP
  refine WP.zero fun hz => ?_
  refine WP.aluImm pa_at_f6 ?_; wn
  refine WP.alu pa_at_f8 ?_; wn
  refine WP.alu pa_at_fa ?_; wn
  refine WP.alu pa_at_fc ?_; wn
  refine WP.callNumberEnd (tb := base + 0xFFFFF372 + 0xFFFFF616 + 0x21A) (out := F + 0xA8) (p := p)
    (n := n) (pos := pos) pa_at_fe pa_at_102 (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) _ (by decide)) (by decide)
    hc1.get.ri.ne (by (try rsimp); rw [hR.sp, ev_add])
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s7)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s8)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h25) (by omega) (by omega)
    (E.alF (d := 0xA8) (by decide)) (E.sepF E.sep.get.ri.ne (d := 0xA8) (w := 8) (by decide))
    (E.sepF E.sep.parse (d := 0xA8) (w := 8) (by decide)) fun m2 hU => ?_
  rw [hd] at hU
  generalize m2.mem = M2 at hU
  have hFI2 : FInv M0 Mp s F n stk M2 := hFI.outF E.hF (d := 0xA8) hU.out (Or.inr ⟨by decide, by decide⟩)
  refine WP.jal pa_at_106 (by decide) ?_; wn
  exact pa_res E hnext hst hU (fun e he => by have := (numberEnd_bd he).2; rwa [memBytes_length] at this) hFI2
    (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h8) (by (try rsimp); exact h26)
    (by (try rsimp); exact h27)

/-- A literal at `0xDA`: the call to `literal_end`, whose frame is the 68
bytes below `F`. -/
theorem pa_lit (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {start pos : Nat} {w27 : Word}
    {stk : List (Bool × Nat)} {M : Word → BitVec 8} {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hnext : PNext M0 Mp base s p out F n c g0 (BitVec.ofNat 32 start) w27 next) (hst : start ≤ n)
    (hFI : FInv M0 Mp s F n stk M) (hR : PRegs f g0 F p n c) (h18 : f 18 = out)
    (h25 : f 25 = BitVec.ofNat 32 pos) (hpos : pos ≤ n) (h8 : f 8 = BitVec.ofNat 32 stk.length)
    (h26 : f 26 = BitVec.ofNat 32 start) (h27 : f 27 = w27) :
    WP jsonParseCode base (PPost M0 s p out g0 (match literalEnd (memBytes M0 p n) pos with
      | none => .error 0x20
      | some e => afterClose (closeLoop c (memBytes M0 p n) start 17 stk e) next)) M 0xDA f := by
  have hfr := hR.fr
  have hn := E.hn
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  have hd : memBytes M p n = memBytes M0 p n := hFI.1.bytes E.sP
  have hso : Sep (F + 0xA8) 8 (s + BitVec.ofNat 32 96) 68 := by
    rw [pa_FA8 E]; exact sep_offsets s (c := 332) (n := 8) (d := 96) (k := 68) (Or.inr (by decide)) (by decide)
      (by decide)
  refine WP.zero fun hz => ?_
  refine WP.aluImm pa_at_da ?_; wn
  refine WP.alu pa_at_dc ?_; wn
  refine WP.alu pa_at_de ?_; wn
  refine WP.alu pa_at_e0 ?_; wn
  refine WP.callLiteralEnd (tb := base + 0xFFFFF372 + 0xFFFFF616 + 0x17E) (out := F + 0xA8)
    (s := s + BitVec.ofNat 32 96) (p := p) (n := n) (pos := pos) pa_at_e2 pa_at_e6
    (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) _ (by decide)) (by decide)
    hc1.get.ri.le (by rw [pi_ad_es]; exact hc1.get.ri.es) (by rw [pi_ad_mc]; exact hc1.get.ri.mc) hc1.get.ri.lit
    (by (try rsimp); rw [hR.sp, ev_add])
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s7)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s8)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h25)
    (by (try rsimp); rw [hR.sp, ← E.hF, add_ofNat_assoc]) (by omega) (by omega)
    (aligned_add E.hal (k := 96) (by decide)) (E.alF (d := 0xA8) (by decide))
    (E.sep.get.ri.le.sub (by decide)) (by rw [pi_ad_es]; exact E.sep.get.ri.es.sub (by decide))
    (by rw [pi_ad_mc]; exact E.sep.get.ri.mc.sub (by decide)) (E.sP.sub (by decide))
    (E.sep.get.ri.ln.sub (by decide)) (E.sep.get.ri.lf.sub (by decide)) hso
    (E.sepF E.sep.get.ri.le (d := 0xA8) (w := 8) (by decide)) (E.sep.parse.sub (by decide))
    (E.sepF E.sep.parse (d := 0xA8) (w := 8) (by decide)) fun m2 hU => ?_
  rw [hd] at hU
  obtain ⟨Ma, hOa, hU⟩ := hU
  generalize m2.mem = M2 at hU
  have hFI2 : FInv M0 Mp s F n stk M2 :=
    (hFI.out E.hF hOa (Or.inl (by decide))).outF E.hF (d := 0xA8) hU.out (Or.inr ⟨by decide, by decide⟩)
  refine WP.jal pa_at_ea (by decide) ?_; wn
  exact pa_res E hnext hst hU (fun e he => by have := (literalEnd_bd he).2; rwa [memBytes_length] at this) hFI2
    (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h8) (by (try rsimp); exact h26)
    (by (try rsimp); exact h27)

end

end C3.RV32
