import C3BootProofs.Proofs.FieldSub

/-!
# Arithmetic for `sub_inner`

`bchain` is the chain of `borrowing_sub` calls `sub_inner` makes, and
`bchain_val` shows it subtracts. `addBack` is the masked addition of `p`
exactly as the compiled code orders its adds and carry checks, and
`addBack_val` shows it adds `p` when the mask is all ones. `sub_fin`
combines them into `subRes`. `omega` proves each step; the 256-bit
identities go through `addBack_fin0` and `addBack_fin1`, which keep the
context small, because `omega` slows down sharply on large contexts with
these coefficients.
-/

namespace C3.RV32

/-- The P-256 modulus. -/
def p256 : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- `x + y` with the carry out, as `add` then `sltu` against the addend computes it. -/
theorem add_carry (x y : Word) :
    (aluEval .add x y).toNat + 2 ^ 32 * (aluEval .sltu (aluEval .add x y) y).toNat = x.toNat + y.toNat := by
  show (x + y).toNat + 2 ^ 32 * (if (x + y).ult y then 1 else 0 : Word).toNat = _
  rw [BitVec.toNat_add]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x.toNat + y.toNat < 2 ^ 32
  · rw [Nat.mod_eq_of_lt h, ite_eq_right (by
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_of_lt h]; exact fun e => by
        have := of_decide_eq_true e; omega)]
    show _ + 2 ^ 32 * 0 = _; omega
  · rw [ite_eq_left (by
      simp only [BitVec.ult, BitVec.toNat_add]; exact decide_eq_true (by omega))]
    show (x.toNat + y.toNat) % 2 ^ 32 + 2 ^ 32 * 1 = _; omega

/-- The `p` limbs that `sub_inner` adds back, as the compiled code adds them:
the words `sub_inner` stores for the differences `d0` to `d7` and the borrow
mask `m`. -/
def addBack (d0 d1 d2 d3 d4 d5 d6 d7 m : Word) : List Word :=
  let s3 := aluEval .add d0 m
  let s4 := aluEval .add d1 m
  let c0 := aluEval .sltu s3 m
  let w1 := aluEval .add c0 s4
  let x2 := aluEval .sltu s4 m
  let y3 := aluEval .sltu w1 s4
  let s5 := aluEval .add d2 m
  let c1 := aluEval .add x2 y3
  let w2 := aluEval .add c1 s5
  let x3 := aluEval .sltu s5 m
  let y4 := aluEval .sltu w2 s5
  let c2 := aluEval .add x3 y4
  let w3 := aluEval .add d3 c2
  let c3 := aluEval .sltu w3 c2
  let w4 := aluEval .add d4 c3
  let m1 := aluEval .and m 1
  let c4 := aluEval .sltu w4 c3
  let s10 := aluEval .add d7 m
  let w5 := aluEval .add d5 c4
  let s9 := aluEval .add d6 m1
  let c5 := aluEval .sltu w5 c4
  let x6 := aluEval .sltu s9 m1
  let w6 := aluEval .add c5 s9
  let y6 := aluEval .sltu w6 s9
  let c6 := aluEval .add x6 y6
  let w7 := aluEval .add c6 s10
  [s3, w1, w2, w3, w4, w5, w6, w7]

/-- Little-endian value of 32-bit limbs. -/
def limbVal : List Word → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 32 * limbVal ws

theorem limbVal_lt : ∀ ws : List Word, limbVal ws < 2 ^ (32 * ws.length)
  | [] => by decide
  | w :: ws => by
    have := w.isLt
    have := limbVal_lt ws
    rw [limbVal, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have h1 : 2 ^ 32 * limbVal ws + 2 ^ 32 ≤ 2 ^ 32 * 2 ^ (32 * ws.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    rw [Nat.mul_comm (2 ^ (32 * ws.length))]
    omega

theorem sltu_le1 (x y : Word) : (aluEval .sltu x y).toNat ≤ 1 := by
  show (if x.ult y then 1 else 0 : Word).toNat ≤ 1
  split <;> decide

theorem add_small {x y : Word} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (aluEval .add x y).toNat = x.toNat + y.toNat := by
  show (x + y).toNat = _
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem addBack_fin0 (Ns3 Nw1 Nw2 Nw3 Nw4 Nw5 Nw6 Nw7 Nd0 Nd1 Nd2 Nd3 Nd4 Nd5 Nd6 Nd7 Nq1 Nq2 : Nat)
    (k7 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nw5 + 6277101735386680763835789423207666416102355444464034512896 * Nw6 +
      26959946667150639794667015087019630673637144422540572481103610249216 * Nw7 + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * (Nq1 + Nq2) = Nd0 + 0 + 4294967296 * (Nd1 + 0) + 18446744073709551616 * (Nd2 + 0) +
      79228162514264337593543950336 * Nd3 + 340282366920938463463374607431768211456 * Nd4 + 1461501637330902918203684832716283019655932542976 * Nd5 + 6277101735386680763835789423207666416102355444464034512896 * (Nd6 + 0) + 26959946667150639794667015087019630673637144422540572481103610249216 * (Nd7 + 0)) :
    Ns3 + 4294967296 * (Nw1 + 4294967296 * (Nw2 + 4294967296 * (Nw3 + 4294967296 * (Nw4 + 4294967296 *
      (Nw5 + 4294967296 * (Nw6 + 4294967296 * Nw7)))))) + 2 ^ 256 * (Nq1 + Nq2) =
    Nd0 + 4294967296 * (Nd1 + 4294967296 * (Nd2 + 4294967296 * (Nd3 + 4294967296 * (Nd4 + 4294967296 *
      (Nd5 + 4294967296 * (Nd6 + 4294967296 * Nd7)))))) + 0 := by
  rw [show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from rfl]
  omega

theorem addBack_fin1 (Ns3 Nw1 Nw2 Nw3 Nw4 Nw5 Nw6 Nw7 Nd0 Nd1 Nd2 Nd3 Nd4 Nd5 Nd6 Nd7 Nq1 Nq2 : Nat)
    (k7 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nw5 + 6277101735386680763835789423207666416102355444464034512896 * Nw6 +
      26959946667150639794667015087019630673637144422540572481103610249216 * Nw7 + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * (Nq1 + Nq2) = Nd0 + 4294967295 + 4294967296 * (Nd1 + 4294967295) + 18446744073709551616 * (Nd2 + 4294967295) +
      79228162514264337593543950336 * Nd3 + 340282366920938463463374607431768211456 * Nd4 + 1461501637330902918203684832716283019655932542976 * Nd5 + 6277101735386680763835789423207666416102355444464034512896 * (Nd6 + 1) + 26959946667150639794667015087019630673637144422540572481103610249216 * (Nd7 + 4294967295)) :
    Ns3 + 4294967296 * (Nw1 + 4294967296 * (Nw2 + 4294967296 * (Nw3 + 4294967296 * (Nw4 + 4294967296 *
      (Nw5 + 4294967296 * (Nw6 + 4294967296 * Nw7)))))) + 2 ^ 256 * (Nq1 + Nq2) =
    Nd0 + 4294967296 * (Nd1 + 4294967296 * (Nd2 + 4294967296 * (Nd3 + 4294967296 * (Nd4 + 4294967296 *
      (Nd5 + 4294967296 * (Nd6 + 4294967296 * Nd7)))))) + 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  rw [show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from rfl]
  omega

/-- **The add-back adds `p` under the mask**: the stored words are the low
256 bits of the differences plus `p` when the mask is all ones. -/
theorem addBack_val (d0 d1 d2 d3 d4 d5 d6 d7 m : Word) (hm : m = 0 ∨ m = 0xFFFFFFFF) :
    limbVal (addBack d0 d1 d2 d3 d4 d5 d6 d7 m) =
      (limbVal [d0, d1, d2, d3, d4, d5, d6, d7] + if m = 0 then 0 else p256) % 2 ^ 256 := by
  have hmn : m.toNat = if m = 0 then 0 else 2 ^ 32 - 1 := by rcases hm with rfl | rfl <;> rfl
  have hm1 : (aluEval .and m 1).toNat = if m = 0 then 0 else 1 := by rcases hm with rfl | rfl <;> rfl
  unfold addBack limbVal
  generalize hs3 : aluEval .add d0 m = s3
  generalize hs4 : aluEval .add d1 m = s4
  generalize hc0 : aluEval .sltu s3 m = c0
  generalize hw1 : aluEval .add c0 s4 = w1
  generalize hx2 : aluEval .sltu s4 m = x2
  generalize hy3 : aluEval .sltu w1 s4 = y3
  generalize hs5 : aluEval .add d2 m = s5
  generalize hc1 : aluEval .add x2 y3 = c1
  generalize hw2 : aluEval .add c1 s5 = w2
  generalize hx3 : aluEval .sltu s5 m = x3
  generalize hy4 : aluEval .sltu w2 s5 = y4
  generalize hc2 : aluEval .add x3 y4 = c2
  generalize hw3 : aluEval .add d3 c2 = w3
  generalize hc3 : aluEval .sltu w3 c2 = c3
  generalize hw4 : aluEval .add d4 c3 = w4
  generalize hm1' : aluEval .and m 1 = m1
  generalize hc4 : aluEval .sltu w4 c3 = c4
  generalize hs10 : aluEval .add d7 m = s10
  generalize hw5 : aluEval .add d5 c4 = w5
  generalize hs9 : aluEval .add d6 m1 = s9
  generalize hc5 : aluEval .sltu w5 c4 = c5
  generalize hx6 : aluEval .sltu s9 m1 = x6
  generalize hw6 : aluEval .add c5 s9 = w6
  generalize hy6 : aluEval .sltu w6 s9 = y6
  generalize hc6 : aluEval .add x6 y6 = c6
  generalize hw7 : aluEval .add c6 s10 = w7
  have e0 := add_carry d0 m; rw [hs3, hc0] at e0
  have e1 := add_carry d1 m; rw [hs4, hx2] at e1
  have e2 := add_carry c0 s4; rw [hw1, hy3] at e2
  have e3 := add_carry d2 m; rw [hs5, hx3] at e3
  have e4 := add_carry c1 s5; rw [hw2, hy4] at e4
  have e5 := add_carry d3 c2; rw [hw3, hc3] at e5
  have e6 := add_carry d4 c3; rw [hw4, hc4] at e6
  have e7 := add_carry d5 c4; rw [hw5, hc5] at e7
  have e8 := add_carry d6 m1; rw [hs9, hx6] at e8
  have e9 := add_carry c5 s9; rw [hw6, hy6] at e9
  have e10 := add_carry d7 m
  rw [hs10] at e10
  have e11 := add_carry c6 s10
  rw [hw7] at e11
  have b0 : c0.toNat ≤ 1 := hc0 ▸ sltu_le1 _ _
  have b2 : x2.toNat ≤ 1 := hx2 ▸ sltu_le1 _ _
  have b3 : y3.toNat ≤ 1 := hy3 ▸ sltu_le1 _ _
  have b4 : x3.toNat ≤ 1 := hx3 ▸ sltu_le1 _ _
  have b5 : y4.toNat ≤ 1 := hy4 ▸ sltu_le1 _ _
  have b6 : x6.toNat ≤ 1 := hx6 ▸ sltu_le1 _ _
  have b7 : y6.toNat ≤ 1 := hy6 ▸ sltu_le1 _ _
  have f1 : c1.toNat = x2.toNat + y3.toNat := hc1 ▸ add_small b2 b3
  have f2 : c2.toNat = x3.toNat + y4.toNat := hc2 ▸ add_small b4 b5
  have f6 : c6.toNat = x6.toNat + y6.toNat := hc6 ▸ add_small b6 b7
  rw [← hm1'] at e8 hs9
  rw [hm1] at e8
  have h7 := w7.isLt; have h6 := w6.isLt; have h5 := w5.isLt; have h4 := w4.isLt
  have h3 := w3.isLt; have h2 := w2.isLt; have h1 := w1.isLt; have h0 := s3.isLt
  have g10 := (aluEval .sltu s10 m).toNat
  have lin : s3.toNat + 4294967296 * (w1.toNat + 4294967296 * (w2.toNat + 4294967296 * (w3.toNat +
      4294967296 * (w4.toNat + 4294967296 * (w5.toNat + 4294967296 * (w6.toNat + 4294967296 * w7.toNat)))))) +
      2 ^ 256 * ((aluEval .sltu s10 m).toNat + (aluEval .sltu w7 s10).toNat) =
      d0.toNat + 4294967296 * (d1.toNat + 4294967296 * (d2.toNat + 4294967296 * (d3.toNat +
      4294967296 * (d4.toNat + 4294967296 * (d5.toNat + 4294967296 * (d6.toNat + 4294967296 * d7.toNat)))))) +
      (if m = 0 then 0 else p256) := by
    rcases hm with rfl | rfl
    · rw [ite_eq_left rfl] at e8 ⊢
      rw [show (0 : Word).toNat = 0 from rfl] at e0 e1 e3 e10
      generalize s3.toNat = Ns3 at *
      generalize w1.toNat = Nw1 at *
      generalize w2.toNat = Nw2 at *
      generalize w3.toNat = Nw3 at *
      generalize w4.toNat = Nw4 at *
      generalize w5.toNat = Nw5 at *
      generalize w6.toNat = Nw6 at *
      generalize w7.toNat = Nw7 at *
      generalize d0.toNat = Nd0 at *
      generalize d1.toNat = Nd1 at *
      generalize d2.toNat = Nd2 at *
      generalize d3.toNat = Nd3 at *
      generalize d4.toNat = Nd4 at *
      generalize d5.toNat = Nd5 at *
      generalize d6.toNat = Nd6 at *
      generalize d7.toNat = Nd7 at *
      generalize c0.toNat = Nc0 at *
      generalize s4.toNat = Ns4 at *
      generalize x2.toNat = Nx2 at *
      generalize y3.toNat = Ny3 at *
      generalize s5.toNat = Ns5 at *
      generalize c1.toNat = Nc1 at *
      generalize x3.toNat = Nx3 at *
      generalize y4.toNat = Ny4 at *
      generalize c2.toNat = Nc2 at *
      generalize c3.toNat = Nc3 at *
      generalize c4.toNat = Nc4 at *
      generalize s10.toNat = Ns10 at *
      generalize c5.toNat = Nc5 at *
      generalize s9.toNat = Ns9 at *
      generalize x6.toNat = Nx6 at *
      generalize y6.toNat = Ny6 at *
      generalize c6.toNat = Nc6 at *
      generalize (aluEval .sltu s10 _).toNat = Nq1 at *
      generalize (aluEval .sltu w7 s10).toNat = Nq2 at *
      clear hmn hm1
      have k1 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * (Nx2 + Ny3) = Nd0 + 0 + 4294967296 * (Nd1 + 0) := by omega
      have k2 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * (Nx3 + Ny4) =
          Nd0 + 0 + 4294967296 * (Nd1 + 0) + 18446744073709551616 * (Nd2 + 0) := by omega
      have k3 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nc3 =
          Nd0 + 0 + 4294967296 * (Nd1 + 0) + 18446744073709551616 * (Nd2 + 0) + 79228162514264337593543950336 * Nd3 := by omega
      have k4 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nc4 =
          Nd0 + 0 + 4294967296 * (Nd1 + 0) + 18446744073709551616 * (Nd2 + 0) + 79228162514264337593543950336 * Nd3 + 340282366920938463463374607431768211456 * Nd4 := by omega
      have k5 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nw5 + 6277101735386680763835789423207666416102355444464034512896 * Nc5 =
          Nd0 + 0 + 4294967296 * (Nd1 + 0) + 18446744073709551616 * (Nd2 + 0) + 79228162514264337593543950336 * Nd3 + 340282366920938463463374607431768211456 * Nd4 + 1461501637330902918203684832716283019655932542976 * Nd5 := by
        omega
      have k6 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nw5 + 6277101735386680763835789423207666416102355444464034512896 * Nw6 +
          26959946667150639794667015087019630673637144422540572481103610249216 * (Nx6 + Ny6) = Nd0 + 0 + 4294967296 * (Nd1 + 0) + 18446744073709551616 * (Nd2 + 0) + 79228162514264337593543950336 * Nd3 +
          340282366920938463463374607431768211456 * Nd4 + 1461501637330902918203684832716283019655932542976 * Nd5 + 6277101735386680763835789423207666416102355444464034512896 * (Nd6 + 0) := by omega
      have k7 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nw5 + 6277101735386680763835789423207666416102355444464034512896 * Nw6 +
          26959946667150639794667015087019630673637144422540572481103610249216 * Nw7 + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * (Nq1 + Nq2) = Nd0 + 0 + 4294967296 * (Nd1 + 0) + 18446744073709551616 * (Nd2 + 0) +
          79228162514264337593543950336 * Nd3 + 340282366920938463463374607431768211456 * Nd4 + 1461501637330902918203684832716283019655932542976 * Nd5 + 6277101735386680763835789423207666416102355444464034512896 * (Nd6 + 0) + 26959946667150639794667015087019630673637144422540572481103610249216 * (Nd7 + 0) := by omega
      exact addBack_fin0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k7
    · rw [ite_eq_right (by decide)] at e8 ⊢
      rw [show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl] at e0 e1 e3 e10
      rw [show p256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951 from rfl]
      generalize s3.toNat = Ns3 at *
      generalize w1.toNat = Nw1 at *
      generalize w2.toNat = Nw2 at *
      generalize w3.toNat = Nw3 at *
      generalize w4.toNat = Nw4 at *
      generalize w5.toNat = Nw5 at *
      generalize w6.toNat = Nw6 at *
      generalize w7.toNat = Nw7 at *
      generalize d0.toNat = Nd0 at *
      generalize d1.toNat = Nd1 at *
      generalize d2.toNat = Nd2 at *
      generalize d3.toNat = Nd3 at *
      generalize d4.toNat = Nd4 at *
      generalize d5.toNat = Nd5 at *
      generalize d6.toNat = Nd6 at *
      generalize d7.toNat = Nd7 at *
      generalize c0.toNat = Nc0 at *
      generalize s4.toNat = Ns4 at *
      generalize x2.toNat = Nx2 at *
      generalize y3.toNat = Ny3 at *
      generalize s5.toNat = Ns5 at *
      generalize c1.toNat = Nc1 at *
      generalize x3.toNat = Nx3 at *
      generalize y4.toNat = Ny4 at *
      generalize c2.toNat = Nc2 at *
      generalize c3.toNat = Nc3 at *
      generalize c4.toNat = Nc4 at *
      generalize s10.toNat = Ns10 at *
      generalize c5.toNat = Nc5 at *
      generalize s9.toNat = Ns9 at *
      generalize x6.toNat = Nx6 at *
      generalize y6.toNat = Ny6 at *
      generalize c6.toNat = Nc6 at *
      generalize (aluEval .sltu s10 _).toNat = Nq1 at *
      generalize (aluEval .sltu w7 s10).toNat = Nq2 at *
      clear hmn hm1
      have k1 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * (Nx2 + Ny3) = Nd0 + 4294967295 + 4294967296 * (Nd1 + 4294967295) := by omega
      have k2 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * (Nx3 + Ny4) =
          Nd0 + 4294967295 + 4294967296 * (Nd1 + 4294967295) + 18446744073709551616 * (Nd2 + 4294967295) := by omega
      have k3 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nc3 =
          Nd0 + 4294967295 + 4294967296 * (Nd1 + 4294967295) + 18446744073709551616 * (Nd2 + 4294967295) + 79228162514264337593543950336 * Nd3 := by omega
      have k4 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nc4 =
          Nd0 + 4294967295 + 4294967296 * (Nd1 + 4294967295) + 18446744073709551616 * (Nd2 + 4294967295) + 79228162514264337593543950336 * Nd3 + 340282366920938463463374607431768211456 * Nd4 := by omega
      have k5 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nw5 + 6277101735386680763835789423207666416102355444464034512896 * Nc5 =
          Nd0 + 4294967295 + 4294967296 * (Nd1 + 4294967295) + 18446744073709551616 * (Nd2 + 4294967295) + 79228162514264337593543950336 * Nd3 + 340282366920938463463374607431768211456 * Nd4 + 1461501637330902918203684832716283019655932542976 * Nd5 := by
        omega
      have k6 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nw5 + 6277101735386680763835789423207666416102355444464034512896 * Nw6 +
          26959946667150639794667015087019630673637144422540572481103610249216 * (Nx6 + Ny6) = Nd0 + 4294967295 + 4294967296 * (Nd1 + 4294967295) + 18446744073709551616 * (Nd2 + 4294967295) + 79228162514264337593543950336 * Nd3 +
          340282366920938463463374607431768211456 * Nd4 + 1461501637330902918203684832716283019655932542976 * Nd5 + 6277101735386680763835789423207666416102355444464034512896 * (Nd6 + 1) := by omega
      have k7 : Ns3 + 4294967296 * Nw1 + 18446744073709551616 * Nw2 + 79228162514264337593543950336 * Nw3 + 340282366920938463463374607431768211456 * Nw4 + 1461501637330902918203684832716283019655932542976 * Nw5 + 6277101735386680763835789423207666416102355444464034512896 * Nw6 +
          26959946667150639794667015087019630673637144422540572481103610249216 * Nw7 + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * (Nq1 + Nq2) = Nd0 + 4294967295 + 4294967296 * (Nd1 + 4294967295) + 18446744073709551616 * (Nd2 + 4294967295) +
          79228162514264337593543950336 * Nd3 + 340282366920938463463374607431768211456 * Nd4 + 1461501637330902918203684832716283019655932542976 * Nd5 + 6277101735386680763835789423207666416102355444464034512896 * (Nd6 + 1) + 26959946667150639794667015087019630673637144422540572481103610249216 * (Nd7 + 4294967295) := by omega
      exact addBack_fin1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k7
  have lin' : limbVal [s3, w1, w2, w3, w4, w5, w6, w7] +
      2 ^ 256 * ((aluEval .sltu s10 m).toNat + (aluEval .sltu w7 s10).toNat) =
      limbVal [d0, d1, d2, d3, d4, d5, d6, d7] + (if m = 0 then 0 else p256) := by
    simp only [limbVal, Nat.mul_zero, Nat.add_zero]; exact lin
  show limbVal [s3, w1, w2, w3, w4, w5, w6, w7] =
    (limbVal [d0, d1, d2, d3, d4, d5, d6, d7] + if m = 0 then 0 else p256) % 2 ^ 256
  rw [← lin', Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (limbVal_lt [s3, w1, w2, w3, w4, w5, w6, w7])).symm

/-- The differences and the final borrow mask of a chain of `borrowing_sub`
calls over two limb lists, from the borrow mask `b`. -/
def bchain : List Word → List Word → Word → List Word × Word
  | l :: ls, r :: rs, b =>
    let d := bsubD l r b
    let r' := bchain ls rs (bsubB l r d)
    (d :: r'.1, r'.2)
  | _, _, b => ([], b)

theorem maskBit_ite (c : Prop) [Decidable c] :
    maskBit (if c then 0xFFFFFFFF else 0) = if c then 1 else 0 := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]; rfl

theorem mask_ite (c : Prop) [Decidable c] :
    (if c then (0xFFFFFFFF : Word) else 0) = 0 ∨ (if c then (0xFFFFFFFF : Word) else 0) = 0xFFFFFFFF := by
  by_cases h : c
  · rw [ite_eq_left h]; exact .inr rfl
  · rw [ite_eq_right h]; exact .inl rfl

/-- **The borrow chain subtracts.** The differences plus `rs` and the borrow
in equal `ls` plus the borrow out at the top, and the final mask is a mask. -/
theorem bchain_val : ∀ (ls rs : List Word) (b : Word), ls.length = rs.length → (b = 0 ∨ b = 0xFFFFFFFF) →
    limbVal (bchain ls rs b).1 + limbVal rs + maskBit b =
      limbVal ls + 2 ^ (32 * ls.length) * maskBit (bchain ls rs b).2 ∧
    ((bchain ls rs b).2 = 0 ∨ (bchain ls rs b).2 = 0xFFFFFFFF)
  | [], [], b, _, hb => ⟨by simp [bchain, limbVal], hb⟩
  | l :: ls, r :: rs, b, h, hb => by
    have hb' := bsubB_eq l r b hb
    obtain ⟨ih, ihm⟩ := bchain_val ls rs (bsubB l r (bsubD l r b)) (by simpa using h)
      (by rw [hb']; exact mask_ite _)
    refine ⟨?_, ihm⟩
    show (bsubD l r b).toNat + 2 ^ 32 * limbVal (bchain ls rs (bsubB l r (bsubD l r b))).1 +
        (r.toNat + 2 ^ 32 * limbVal rs) + maskBit b =
      l.toNat + 2 ^ 32 * limbVal ls + 2 ^ (32 * (ls.length + 1)) * maskBit (bchain ls rs (bsubB l r (bsubD l r b))).2
    have hmb : maskBit (bsubB l r (bsubD l r b)) = if l.toNat < r.toNat + maskBit b then 1 else 0 := by
      rw [hb', maskBit_ite]
    rw [hmb] at ih
    have hd := bsubD_toNat l r b hb
    have hm : maskBit b ≤ 1 := by unfold maskBit; split <;> decide
    have hl := l.isLt; have hr := r.isLt
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (32 * ls.length)) (2 ^ 32), Nat.mul_assoc]
    generalize limbVal (bchain ls rs (bsubB l r (bsubD l r b))).1 = D at ih ⊢
    generalize 2 ^ (32 * ls.length) * maskBit (bchain ls rs (bsubB l r (bsubD l r b))).2 = QC at ih ⊢
    by_cases hc : l.toNat < r.toNat + maskBit b
    · rw [ite_eq_left hc] at ih
      omega
    · rw [ite_eq_right hc] at ih
      omega

/-- What `sub_inner` leaves for `L`: `L - p` when `L` is at least `p`, and
`L` otherwise, in 256 bits. -/
def subRes (L : Nat) : Nat := if L < p256 then L % 2 ^ 256 else (L - p256) % 2 ^ 256

set_option exponentiation.threshold 300 in
theorem sub_fin (D8 d8 L c : Nat) (hD8 : D8 < 2 ^ 256) (hc : c ≤ 1)
    (h : D8 + 2 ^ 256 * d8 + p256 = L + 2 ^ 288 * c) (hd8 : d8 < 2 ^ 32) :
    (D8 + if c = 0 then 0 else p256) % 2 ^ 256 = subRes L ∧ (c = 1 ↔ L < p256) := by
  unfold subRes
  rw [show p256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951 from rfl] at h ⊢
  rw [show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from rfl] at hD8 h ⊢
  rw [show (2 : Nat) ^ 288 = 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 from rfl] at h
  rw [show (2 : Nat) ^ 32 = 4294967296 from rfl] at hd8
  by_cases h0 : c = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ L < 115792089210356248762697446949407573530086143415290314195533631308867097853951)]
    exact ⟨by omega, fun e => absurd e (by decide), fun e => absurd e (by omega)⟩
  · have h1 : c = 1 := by omega
    subst h1
    rw [ite_eq_right (by decide), ite_eq_left (by omega : L < 115792089210356248762697446949407573530086143415290314195533631308867097853951)]
    exact ⟨by omega, fun _ => by omega, fun _ => rfl⟩

/-- What `sub_inner` stores for 9-limb numbers `L` and `R`: `L - R`, with `p`
added back when it borrows, in 256 bits. -/
def subGen (L R : Nat) : Nat := if L < R then (L + 2 ^ 288 + p256 - R) % 2 ^ 256 else (L - R) % 2 ^ 256

set_option exponentiation.threshold 300 in
theorem sub_fin_gen (D8 d8 L R c : Nat) (hD8 : D8 < 2 ^ 256) (hc : c ≤ 1)
    (h : D8 + 2 ^ 256 * d8 + R = L + 2 ^ 288 * c) (hd8 : d8 < 2 ^ 32) :
    (D8 + if c = 0 then 0 else p256) % 2 ^ 256 = subGen L R ∧ (c = 1 ↔ L < R) := by
  unfold subGen
  rw [show p256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951 from rfl]
  rw [show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from rfl] at hD8 h ⊢
  rw [show (2 : Nat) ^ 288 = 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 from rfl] at h ⊢
  rw [show (2 : Nat) ^ 32 = 4294967296 from rfl] at hd8
  by_cases h0 : c = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ L < R)]
    exact ⟨by omega, fun e => absurd e (by decide), fun e => absurd e (by omega)⟩
  · have h1 : c = 1 := by omega
    subst h1
    rw [ite_eq_right (by decide), ite_eq_left (by omega : L < R)]
    exact ⟨by omega, fun _ => by omega, fun _ => rfl⟩

set_option exponentiation.threshold 300 in
theorem subGen_p (L : Nat) : subGen L p256 = subRes L := by
  unfold subGen subRes
  by_cases h : L < p256
  · rw [ite_eq_left h, ite_eq_left h]
    rw [show p256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951 from rfl] at h ⊢
    rw [show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from rfl, show (2 : Nat) ^ 288 = 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056 from rfl]
    omega
  · rw [ite_eq_right h, ite_eq_right h]

end C3.RV32
