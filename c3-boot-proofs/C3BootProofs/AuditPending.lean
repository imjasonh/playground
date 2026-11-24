import C3BootProofs.Audit
import C3BootProofs.Proofs.Boot

/-!
# Pending audit

The non-vacuity theorems and axiom pins that `Audit` held for the pending
modules. `Pending` imports this file, so the root module doesn't.
-/

namespace C3

/-- info: 'C3.RV32.Cur.boot_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.boot_correct

end C3
