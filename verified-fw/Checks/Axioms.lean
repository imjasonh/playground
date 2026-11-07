/-
Fails the build if a top-level theorem depends on `sorry` or on any axiom
besides Lean's three standard ones. That rules out `native_decide` and
`bv_decide`, which trust compiled code instead of the kernel.
-/
import Lean
import VerifiedFw

open Lean Elab Command

elab "#assert_standard_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axioms.filter fun a => !allowed.contains a
  unless bad.isEmpty do
    throwError "{name} depends on {bad.toList}"

#assert_standard_axioms VerifiedFw.RiscV.decode_encode
#assert_standard_axioms VerifiedFw.Compiler.compile_correct
#assert_standard_axioms VerifiedFw.Compiler.codeAt_image
#assert_standard_axioms VerifiedFw.qemuVirt_correct
#assert_standard_axioms VerifiedFw.esp32c3_correct
#assert_standard_axioms VerifiedFw.Examples.counter_on_qemu
#assert_standard_axioms VerifiedFw.Examples.Blinky.blinky_on_esp32c3
