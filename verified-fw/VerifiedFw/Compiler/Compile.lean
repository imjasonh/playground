/-
The compiler from the firmware language to RV32I. It is not trusted:
`Compiler/Correct.lean` proves that the code it emits does what the source
semantics says.

Register use:
* `x3` (`gp`) holds the address of global 0 for the whole run.
* `x5` and up hold expression temporaries, one per level of nesting.

Each loop keeps its counter in a RAM slot after the globals, one slot per
level of loop nesting.
-/
import VerifiedFw.RiscV.Encode
import VerifiedFw.Lang.Semantics

namespace VerifiedFw.Compiler

open VerifiedFw.RiscV VerifiedFw.Lang

/-- Where a program goes on a particular chip. -/
structure Target where
  platform : Platform
  /-- Address of the first instruction. -/
  codeBase : Word
  /-- Address of global 0. Loop counters follow the globals. -/
  dataBase : Word

def zero : Reg := 0
def gp : Reg := 3

/-- The register for an expression temporary at nesting depth `d`. -/
def tmp (d : Nat) : Reg := ⟨(5 + d) % 32, Nat.mod_lt _ (by decide)⟩

/-- Offset from `gp` of global `i`, or of loop counters after the globals. -/
def slot (i : Nat) : BitVec 12 := .ofNat 12 (4 * i)

/-- A `jal` offset field for a jump of `delta` instructions. -/
def jumpBy (delta : Int) : BitVec 20 := .ofInt 20 (2 * delta)

/-- Loads any 32-bit constant: `lui` sets the upper bits and `addi` adds the
sign-extended low 12. -/
def loadImm (rd : Reg) (c : Word) : List Instr :=
  let lo : BitVec 12 := c.setWidth 12
  [.lui rd (((c - sext12 lo) >>> 12).setWidth 20), .addi rd rd lo]

def binInstr : BinOp → Reg → Reg → Reg → Instr
  | .add => .add | .sub => .sub | .and => .and | .or => .or | .xor => .xor
  | .shl => .sll | .shr => .srl | .ltu => .sltu

/-- Leaves the value of `e` in `tmp d`, using only `tmp d` and above. -/
def compileExpr : Expr → Nat → List Instr
  | .const c, d => loadImm (tmp d) c
  | .var i, d => [.lw (tmp d) gp (slot i)]
  | .bin op a b, d =>
    compileExpr a d ++ compileExpr b (d + 1) ++ [binInstr op (tmp d) (tmp d) (tmp (d + 1))]

/-- Compiles a statement. `g` is the number of globals and `k` the number of
enclosing loops. -/
def compileStmt (g : Nat) : Stmt → Nat → List Instr
  | .skip, _ => []
  | .assign i e, _ => compileExpr e 0 ++ [.sw (tmp 0) gp (slot i)]
  | .store a e, _ => compileExpr e 0 ++ loadImm (tmp 1) a ++ [.sw (tmp 0) (tmp 1) 0]
  | .seq a b, k => compileStmt g a k ++ compileStmt g b k
  | .ite c t e, k =>
    let ct := compileStmt g t k
    let ce := compileStmt g e k
    compileExpr c 0 ++
      [.bne (tmp 0) zero 4, .jal zero (jumpBy (ct.length + 2))] ++
      ct ++ [.jal zero (jumpBy (ce.length + 1))] ++ ce
  | .loop n body, k =>
    let cb := compileStmt g body (k + 1)
    loadImm (tmp 0) (.ofNat 32 n) ++ [.sw (tmp 0) gp (slot (g + k))] ++
      [.lw (tmp 0) gp (slot (g + k)),
       .bne (tmp 0) zero 4,
       .jal zero (jumpBy (cb.length + 4)),
       .addi (tmp 0) (tmp 0) (-1),
       .sw (tmp 0) gp (slot (g + k))] ++
      cb ++ [.jal zero (jumpBy (-((cb.length : Int) + 5)))]

def prologue (t : Target) (p : Program) : List Instr :=
  loadImm gp t.dataBase ++ (List.range p.globals).map fun i => .sw zero gp (slot i)

/-- The whole image: set up `gp`, zero the globals, run the body, then jump
to the same instruction forever. -/
def compile (t : Target) (p : Program) : List Instr :=
  prologue t p ++ compileStmt p.globals p.body 0 ++ [.jal zero 0]

end VerifiedFw.Compiler

namespace VerifiedFw.Lang

open VerifiedFw.RiscV VerifiedFw.Compiler

/-! ## Well-formedness

The compiler only promises correct code for programs that pass `Program.wf`.
These checks are decidable, so a concrete program discharges them with
`decide`. -/

/-- How many temporaries `compileExpr` needs. -/
def Expr.regs : Expr → Nat
  | .const _ | .var _ => 1
  | .bin _ a b => max a.regs (b.regs + 1)

def Expr.varsBelow (g : Nat) : Expr → Bool
  | .const _ => true
  | .var i => i < g
  | .bin _ a b => a.varsBelow g && b.varsBelow g

def Stmt.loopDepth : Stmt → Nat
  | .skip | .assign _ _ | .store _ _ => 0
  | .seq a b | .ite _ a b => max a.loopDepth b.loopDepth
  | .loop _ b => b.loopDepth + 1

def Stmt.wf (t : Target) (g : Nat) : Stmt → Bool
  | .skip => true
  | .assign i e => i < g && e.varsBelow g && e.regs ≤ 27
  | .store a e =>
    t.platform.isMmio a && a.toNat % 4 == 0 && e.varsBelow g && e.regs ≤ 27
  | .seq a b => a.wf t g && b.wf t g
  | .ite c a b => c.varsBelow g && c.regs ≤ 27 && a.wf t g && b.wf t g
  | .loop n b => n < 2 ^ 32 && b.wf t g

/-- The model keeps instructions and data in separate memories, which matches
the hardware only if no RAM slot overlaps the code. -/
def Program.wf (t : Target) (p : Program) : Bool :=
  let codeEnd := t.codeBase.toNat + 4 * (compile t p).length
  p.body.wf t p.globals &&
  p.globals + p.body.loopDepth ≤ 512 &&
  (compile t p).length < 2 ^ 17 &&
  t.codeBase.toNat % 4 == 0 &&
  t.dataBase.toNat % 4 == 0 &&
  (List.range (p.globals + p.body.loopDepth)).all fun i =>
    let a := t.dataBase + .ofNat 32 (4 * i)
    !t.platform.isMmio a && !(t.codeBase.toNat ≤ a.toNat && a.toNat < codeEnd)

end VerifiedFw.Lang
