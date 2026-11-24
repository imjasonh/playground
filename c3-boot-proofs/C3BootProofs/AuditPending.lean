import C3BootProofs.Audit
import C3BootProofs.Proofs.X509ReadTime
import C3BootProofs.Proofs.ParseCur
import C3BootProofs.Proofs.Boot

/-!
# Pending audit

The non-vacuity theorems and axiom pins that `Audit` held for the pending
modules. `Pending` imports this file, so the root module doesn't.
-/

namespace C3

/-- A machine that calls `time::generalized_time` on 15 bytes at
`0x3FCC7000`, with the result at `0x3FCC5000` and the stack at `0x3FCC8000`,
meets `generalizedTime_correct`'s hypotheses. -/
theorem exists_generalizedTime_machine :
    ∃ (m : RV32.Machine) (sp0 out p retAddr : RV32.Word) (n : Nat),
      RV32.CodeIn m.mem RV32.GNT Image.generalizedTimeCode ∧ RV32.CodeIn m.mem RV32.DT Image.dateTimeCode ∧
      RV32.CodeIn m.mem RV32.TD Image.timeDigits2Code ∧ m.pc = RV32.GNT ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = p ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x60 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat + 16 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧ n < 2 ^ 32 ∧
      p.toNat + n + 14 ≤ 0x40000000 ∧ 0 < p.toNat ∧ RV32.Sep out 16 (sp0 + 0xFFFFFFA0) 0x60 ∧
      RV32.Sep p (n + 14) (sp0 + 0xFFFFFFA0) 0x60 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC7000 15, RV32.GNT, witnessMemGT⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC7000, 0, 15,
    by code_in, by code_in, by code_in, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩

/-- A machine that calls `x509::read_time` on a DER reader at `0x3FCC6000`
over 17 bytes, with the result at `0x3FCC5000` and the stack at
`0x3FCC8000`, meets `x509ReadTime_correct`'s hypotheses. -/
theorem exists_x509ReadTime_machine :
    ∃ (m : RV32.Machine) (sp0 out d rp retAddr : RV32.Word) (rl : Nat),
      RV32.CodeIn m.mem RV32.XRT Image.x509ReadTimeCode ∧ RV32.CodeIn m.mem RV32.TLV Image.derTlvCode ∧
      RV32.CodeIn m.mem RV32.GNT Image.generalizedTimeCode ∧ RV32.CodeIn m.mem RV32.DT Image.dateTimeCode ∧
      RV32.CodeIn m.mem RV32.TD Image.timeDigits2Code ∧ m.pc = RV32.XRT ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = d ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x60 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧
      out.toNat + 16 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧ d.toNat + 16 ≤ 0x40000000 ∧ d.toNat % 4 = 0 ∧
      RV32.memLoad32 m.mem (d + 8) = rp ∧ RV32.memLoad32 m.mem (d + 0xC) = BitVec.ofNat 32 rl ∧
      rp.toNat + rl + 14 ≤ 0x40000000 ∧ 0 < rp.toNat ∧ RV32.Sep out 16 (sp0 + 0xFFFFFFA0) 0x60 ∧
      RV32.Sep (d + 8) 8 (sp0 + 0xFFFFFFA0) 0x60 ∧ RV32.Sep out 16 (d + 8) 8 ∧
      RV32.Sep rp (rl + 14) (sp0 + 0xFFFFFFA0) 0x60 ∧ RV32.Sep rp rl (d + 8) 8 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, RV32.XRT, witnessMemXRT⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000,
    0x3FCC7000, 0, 17, by code_in, by code_in, by code_in, by code_in, by code_in, rfl, rfl, rfl, rfl, by decide, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide, by decide, RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm⟩

/-- info: 'C3.RV32.generalizedTime_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.generalizedTime_correct

/-- info: 'C3.RV32.gnt_year' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.gnt_year

/-- info: 'C3.RV32.gnt_frac' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.gnt_frac

/-- info: 'C3.RV32.gtTail_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.gtTail_mem

/-- info: 'C3.RV32.x509ReadTime_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.x509ReadTime_correct

/-- info: 'C3.RV32.derTlvMem_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derTlvMem_ok

/-- info: 'C3.RV32.readTime_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readTime_ok

/-- info: 'C3.RV32.Cur.manifestParse_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.manifestParse_correct

/-- info: 'C3.RV32.Cur.boot_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.boot_correct

end C3
