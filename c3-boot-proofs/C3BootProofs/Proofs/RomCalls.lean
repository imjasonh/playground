import C3BootProofs.Proofs.FlashRead

/-!
# ROM routines

The bootloader calls routines in the ESP32-C3's mask ROM, whose code the
image doesn't contain. `RomFn` is what the proofs assume about one: called
at its address with the ROM's code in memory, arguments that satisfy `pre`,
and `stack` bytes of stack below `sp`, it returns to `ra` with the
registers `romKeep` names unchanged and memory outside its stack unchanged.
What it returns in `a0` and what it does outside memory, such as writing
flash, are left open. A proof that uses a contract must show each call
meets its `pre`, so the contract also records what the caller passes.
-/

namespace C3.RV32

/-- What the proofs assume about the ROM routine at `addr`. -/
def RomFn (romBase : Word) (romCode : List Nat) (addr : Word) (stack : Nat) (pre : Machine → Prop) : Prop :=
  ∀ m : Machine, CodeIn m.mem romBase romCode → m.pc = addr → pre m → stack ≤ (reg m sp).toNat →
    ∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp - BitVec.ofNat 32 stack) stack x 1 → m'.mem x = m.mem x

end C3.RV32
