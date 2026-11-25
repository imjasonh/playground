import C3BootProofs.Proofs.TufRoleKeysMetCmp
import C3BootProofs.Proofs.Dec384Main
import C3BootProofs.Image.BootloaderData5
import C3BootProofs.Image.BootloaderData7
import C3BootProofs.Proofs.P2vP256
import C3BootProofs.Proofs.Ed25519VerifyC
import C3BootProofs.Proofs.Sha384Fn
import C3BootProofs.Proofs.Sha2OneShot
import C3BootProofs.Proofs.EcdsaSig32
import C3BootProofs.Proofs.SvDerBridge
import C3BootProofs.Proofs.SmallFns
import C3BootProofs.Models.EcdsaClosed
import C3BootProofs.Models.Ed25519Closed
import C3BootProofs.Models.SafegcdP384
import C3BootProofs.Models.P256Consts

/-!
# The calls in `RoleKeys::met`

`met` calls three signature checks, two hashes, two DER signature parsers,
and three key comparisons. Each lemma here turns one callee's contract into
the `WP` form of a call: the callee's result, the registers it keeps, and
the memory outside its stack and output that it leaves alone.

The callees' contracts come in three styles: a frame structure with saved
registers (`P2vRet`, `p384VerifyPrehash_correct`), a list of saved registers
(`ed25519Verify_correct`, `sha384Fn_correct`), and a list of changed
registers (`sha256Fn_correct`, the DER parsers, the comparisons). One
lemma for each style, `tmc_keepSaved`, `tmc_keepPs`, and `tmc_keepVal`,
gives the registers outside `jClob` that the call keeps.

A signature check that returns nonzero gives the specification's check at
once, through the closed models: `p256_model_closed`, `p384_model_closed`,
and `svEdModel_closed`. A check may also panic; `WP.callGenP` passes that
to the postcondition.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.P2v C3.RV32.Pv C3.RV32.Sv C3.RV32.Dq C3.RV32.P3

theorem tmc_reg0 (m n : Machine) : reg n 0 = reg m 0 := rfl

theorem tmc_svBytes (M : Word → BitVec 8) (p : Word) {n : Nat} : svBytes (memBytes M p n) n = memBytes M p n :=
  (memBytes_svBytes fun j hj => by rw [memBytes_getD hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]).symm

/-- A callee that restores `sp`, `gp`, `tp`, and the 13 registers that
`savedReg` lists keeps every register outside `jClob`. -/
theorem tmc_keepSaved {m n : Machine} (hs : ∀ k, k < 13 → reg n (savedReg k) = reg m (savedReg k))
    (h2 : reg n sp = reg m sp) (h3 : reg n (3 : Fin 32) = reg m (3 : Fin 32))
    (h4 : reg n (4 : Fin 32) = reg m (4 : Fin 32)) : ∀ x, x ∉ jClob → reg n x = reg m x := by
  intro x hx
  have hq : x = 0 ∨ x = sp ∨ x = 3 ∨ x = 4 ∨ x = savedReg 0 ∨ x = savedReg 1 ∨ x = savedReg 2 ∨
      x = savedReg 3 ∨ x = savedReg 4 ∨ x = savedReg 5 ∨ x = savedReg 6 ∨ x = savedReg 7 ∨ x = savedReg 8 ∨
      x = savedReg 9 ∨ x = savedReg 10 ∨ x = savedReg 11 ∨ x = savedReg 12 := by
    revert hx; revert x; decide
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tmc_reg0 m n
  · exact h2
  · exact h3
  · exact h4
  all_goals exact hs _ (by decide)

/-- A callee that restores `sp`, `gp`, `tp`, and the registers in `ps`
keeps every register outside `jClob ++ extra`, when `ps` and `extra` cover
the registers `savedReg` lists. -/
theorem tmc_keepPs {m n : Machine} {ps : List (Fin 32 × Word)} (extra : List (Fin 32))
    (hc : ∀ k, k < 13 → savedReg k ∈ extra ∨ savedReg k ∈ ps.map Prod.fst)
    (hs : ∀ r o, (r, o) ∈ ps → reg n r = reg m r)
    (h2 : reg n sp = reg m sp) (h3 : reg n (3 : Fin 32) = reg m (3 : Fin 32))
    (h4 : reg n (4 : Fin 32) = reg m (4 : Fin 32)) : ∀ x, x ∉ jClob ++ extra → reg n x = reg m x := by
  intro x hx
  have hj : x ∉ jClob := fun h => hx (List.mem_append_left _ h)
  have he : x ∉ extra := fun h => hx (List.mem_append_right _ h)
  have hq : x = 0 ∨ x = sp ∨ x = 3 ∨ x = 4 ∨ ∃ k, k < 13 ∧ x = savedReg k := by
    clear hx he; revert hj; revert x; decide
  rcases hq with rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩
  · exact tmc_reg0 m n
  · exact h2
  · exact h3
  · exact h4
  · rcases hc k hk with h | h
    · exact absurd h he
    · obtain ⟨⟨r, o⟩, hm, hr⟩ := List.mem_map.mp h
      dsimp only at hr; subst hr
      exact hs _ o hm

/-- A callee that keeps every register whose index `l` lists keeps every
register outside `jClob`, when `l` covers sp, gp, tp, and `savedReg`. -/
theorem tmc_keepVal {m n : Machine} (h : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
    reg n q = reg m q) : ∀ x, x ∉ jClob → reg n x = reg m x := by
  intro x hx
  have hq : x = 0 ∨ x.val ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
    revert hx; revert x; decide
  rcases hq with rfl | hq
  · exact tmc_reg0 m n
  · exact h x hq

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- `WP.callGen` for a callee that may panic instead of returning. -/
theorem WP.callGenP {cl : List (Fin 32)} {P : Machine → Prop} {hi lo tb : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (base + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = tb)
    (hQ : ∀ m, Halting m → Q m.pc m.mem (reg m))
    (hcallee : ∀ m1 : Machine, m1.pc = tb → m1.mem = M →
      (∀ x, reg m1 x = upd f ra (base + BitVec.ofNat 32 (off + 8)) x) → base.toNat % 2 = 0 →
      Panics m1 ∨
      ∃ m2, Steps m1 m2 ∧ m2.pc = base + BitVec.ofNat 32 (off + 8) ∧ P m2 ∧ ∀ x, x ∉ cl → reg m2 x = reg m1 x)
    (hcode : ∀ m2 : Machine, P m2 → CodeIn M base code → CodeIn m2.mem base code)
    (k : ∀ m2 : Machine, P m2 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 cl)) :
    WP code base Q M off f := by
  refine WP.call h1 h2 fun m1 hpc1 hmem1 hreg1 hb hc => ?_
  rcases hcallee m1 (by rw [hpc1, htgt]) hmem1 hreg1 hb with ⟨m2, c2, hh⟩ | ⟨m2, c2, pc2, hP, hfr⟩
  · exact ⟨m2, c2, hQ m2 hh⟩
  · refine WP.resume c2 pc2 (fun x => ?_) hb (hcode m2 hP hc) (k m2 hP)
    by_cases hx : x ∈ cl
    · simp only [clob_app, hx, ↓reduceIte]
    · simp only [clob_app, hx, ↓reduceIte]; rw [hfr x hx, hreg1]

/-- A call to `p256_verify_prehash(pk, dg, r, s)`. A nonzero result means
`p256Verify` accepts the key, digest, and signature in memory. -/
theorem WP.callP2vM {hi lo B pk dg rp sq : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = P2V) (hev : (off + 8) % 2 = 0)
    (hQ : ∀ m, Halting m → Q m.pc m.mem (reg m))
    (E : P2vEnv M) (K : C3.Models.P256Consts M) (F : Fr B 0x3590) (RS : P2vRoSep B)
    (hsp : f sp = B + 0x3590) (h0 : f a0 = pk) (ha1 : f a1 = dg) (ha2 : f a2 = rp) (ha3 : f a3 = sq)
    (r_in : P2vIn B rp 32) (s_in : P2vIn B sq 32) (k_in : P2vIn B pk 0x41) (dg_in : P2vIn B dg 32)
    (hSb : Sep (B + 0xFFFFFE60) 0x3730 base code.length)
    (k : ∀ m2 : Machine, (reg m2 a0 ≠ 0 →
        p256Verify (memBytes M pk 65) (memBytes M dg 32) (memBytes M rp 32) (memBytes M sq 32) = true) →
      Out M m2.mem (B + 0xFFFFFE60) 0x3730 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGenP (tb := P2V) (cl := jClob)
    (P := fun m2 => (reg m2 a0 ≠ 0 →
        p256Verify (memBytes M pk 65) (memBytes M dg 32) (memBytes M rp 32) (memBytes M sq 32) = true) ∧
      Out M m2.mem (B + 0xFFFFFE60) 0x3730)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) hQ (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc hSb) (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  have hra : reg m1 ra = base + BitVec.ofNat 32 (off + 8) := by rw [hreg1]; rsimp
  rcases p256VerifyPrehash_correct m1 (by rw [hmem1]; exact E) F hpc1 (by rw [hr sp (by decide), hsp])
      (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1]) (by rw [hr a2 (by decide), ha2])
      (by rw [hr a3 (by decide), ha3]) (by rw [hra]; exact even_clear _ (even_at base hb _ hev))
      RS r_in s_in k_in dg_in with hp | ⟨m2, c2, pc2, sp2, sv2, g3, g4, a02, mem2⟩ |
      ⟨hf, m2, c2, pc2, sp2, sv2, g3, g4, a02, mem2⟩
  · exact .inl hp
  · refine .inr ⟨m2, c2, pc2.trans hra, ⟨fun h => absurd a02 h, fun x hx => by rw [mem2 x hx.symm, hmem1]⟩,
      tmc_keepSaved sv2 (by rw [sp2, hr sp (by decide), hsp]) g3 g4⟩
  · rw [hmem1] at hf
    refine .inr ⟨m2, c2, pc2.trans hra, ⟨fun _ => ?_, fun x hx => by rw [mem2 x hx.symm, hmem1]⟩,
      tmc_keepSaved sv2 (by rw [sp2, hr sp (by decide), hsp]) g3 g4⟩
    have := C3.Models.p256_model_closed K pk dg _ _ hf
    rwa [b32_mem, b32_mem] at this

/-- A call to `p384_verify_prehash(pk, ph, 48, r, s)`. A nonzero result
means `p384Verify` accepts the key, prehash, and signature in memory. -/
theorem WP.callPvM {hi lo B pk ph rp sq : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = PV) (hev : (off + 8) % 2 = 0)
    (hQ : ∀ m, Halting m → Q m.pc m.mem (reg m))
    (E : PvEnv7 M) (F : Fr B 0x21A0)
    (hsp : f sp = B + 0x21A0) (h0 : f a0 = pk) (ha1 : f a1 = ph) (ha2 : f a2 = BitVec.ofNat 32 48)
    (ha3 : f a3 = rp) (ha4 : f a4 = sq)
    (sPK : Sep pk 0x61 (B + 0xFFFFFE60) 0x2340) (hPK : pk.toNat + 0x61 ≤ 0x40000000)
    (sR : Sep rp 48 (B + 0xFFFFFE60) 0x2340) (sS : Sep sq 48 (B + 0xFFFFFE60) 0x2340)
    (sph : Sep ph 48 (B + 0xFFFFFE60) 0x2340) (hph : ph.toNat + 48 < 2 ^ 32)
    (hSb : Sep (B + 0xFFFFFE60) 0x2340 base code.length)
    (k : ∀ m2 : Machine, (reg m2 a0 ≠ 0 →
        p384Verify (memBytes M pk 0x61) (memBytes M ph 48) (memBytes M rp 48) (memBytes M sq 48) = true) →
      Out M m2.mem (B + 0xFFFFFE60) 0x2340 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGenP (tb := PV) (cl := jClob)
    (P := fun m2 => (reg m2 a0 ≠ 0 →
        p384Verify (memBytes M pk 0x61) (memBytes M ph 48) (memBytes M rp 48) (memBytes M sq 48) = true) ∧
      Out M m2.mem (B + 0xFFFFFE60) 0x2340)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) hQ (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc hSb) (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  rcases p384VerifyPrehash_correct m1 (by rw [hmem1]; exact E) F hpc1 (by rw [hr sp (by decide), hsp])
      (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1]) (by rw [hr a2 (by decide), ha2])
      (by rw [hr a3 (by decide), ha3]) (by rw [hr a4 (by decide), ha4]) (by rw [hreg1]; rsimp)
      (even_clear _ (even_at base hb _ hev)) sPK hPK sR sS sph hph
      (C3.RV32.Safegcd.pvSide_holds _ _ _ _ _ _) with
      ⟨-, hp⟩ | ⟨v, hv, m2, c2, pc2, sp2, sv2, g3, g4, a02, mem2⟩
  · exact .inl hp
  · rw [hmem1] at hv mem2
    refine .inr ⟨m2, c2, pc2, ⟨fun hne => ?_, fun x hx => mem2 x hx.symm⟩,
      tmc_keepSaved sv2 (by rw [sp2, hr sp (by decide), hsp]) g3 g4⟩
    have hat : SvPvAt M M pk ph 48 (memBytes M ph 48) rp sq (memBytes M rp 48) (memBytes M sq 48) :=
      ⟨rfl, rfl, by rw [Nat.min_self], (tmc_svBytes M rp).symm, (tmc_svBytes M sq).symm⟩
    have := C3.Models.p384_model_closed pk ph 48 _ rp sq _ _ v ⟨M, hat⟩ (by rw [← hv]; exact SvPvRes.of hat)
      (by rw [← a02]; exact hne)
    rwa [tmc_svBytes, tmc_svBytes] at this

/-- A call to `ed25519_verify(pk, msg, len, sig)`. A nonzero result means
`ed25519Verify` accepts the key, message, and signature in memory. -/
theorem WP.callEdM {hi lo F pk sig msg : Word} {len : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = EV) (hev : (off + 8) % 2 = 0)
    (C : EvCtx M F pk sig msg len) (I : EdM.EdImage M) (K : EdK.KImage M)
    (hsp : f sp = F + BitVec.ofNat 32 0x16A0) (h0 : f a0 = pk) (ha1 : f a1 = msg)
    (ha2 : f a2 = BitVec.ofNat 32 len) (ha3 : f a3 = sig)
    (hSb : Sep (evG F) 0x20B0 base code.length)
    (k : ∀ m2 : Machine, (reg m2 a0 ≠ 0 →
        ed25519Verify (memBytes M pk 32) (memBytes M msg len) (memBytes M sig 64) = true) →
      Out M m2.mem (evG F) 0x20B0 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := EV) (cl := jClob)
    (P := fun m2 => (reg m2 a0 ≠ 0 →
        ed25519Verify (memBytes M pk 32) (memBytes M msg len) (memBytes M sig 64) = true) ∧
      Out M m2.mem (evG F) 0x20B0)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc hSb) (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  have hra : reg m1 ra = base + BitVec.ofNat 32 (off + 8) := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, sp2, rs2, g3, g4, a02, mem2⟩ := ed25519Verify_correct m1 (by rw [hmem1]; exact C) hpc1
    (by rw [hr sp (by decide), hsp]) (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1])
    (by rw [hr a2 (by decide), ha2]) (by rw [hr a3 (by decide), ha3])
    (by rw [hra]; exact even_clear _ (even_at base hb _ hev))
  rw [hmem1] at a02 mem2
  refine ⟨m2, c2, pc2.trans hra, ⟨fun hne => ?_, fun x hx => mem2 x hx.symm⟩, fun x hx => ?_⟩
  · cases he : evSpec M pk sig msg len
    · rw [he] at a02; exact absurd a02 hne
    · exact EdM.svEdModel_closed I K pk sig msg len he
  · exact tmc_keepPs [] (ps := evPs) (by decide) rs2 sp2 g3 g4 x (by rw [List.append_nil]; exact hx)

/-- A call to `sha384(out, p, len)`. -/
theorem WP.callSha384M {hi lo F out p : Word} {len : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = HF) (hev : (off + 8) % 2 = 0)
    (C : HfCtx M F out p len) (hsp : f sp = F + BitVec.ofNat 32 0x240) (h0 : f a0 = out) (ha1 : f a1 = p)
    (ha2 : f a2 = BitVec.ofNat 32 len)
    (hSb : Sep (hfG F) 0x660 base code.length) (hOb : Sep out 48 base code.length)
    (k : ∀ m2 : Machine, memBytes m2.mem out 48 = sha384 (memBytes M p len) →
      (∀ x, Sep x 1 (hfG F) 0x660 → Sep x 1 out 48 → m2.mem x = M x) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 (jClob ++ [27]))) :
    WP code base Q M off f := by
  refine WP.callGen (tb := HF) (cl := jClob ++ [27])
    (P := fun m2 => memBytes m2.mem out 48 = sha384 (memBytes M p len) ∧
      (∀ x, Sep x 1 (hfG F) 0x660 → Sep x 1 out 48 → m2.mem x = M x))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => by rw [hP.2 _ (sep_pt hSb hi) (sep_pt hOb hi)]; exact hc i hi)
    (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  have hra : reg m1 ra = base + BitVec.ofNat 32 (off + 8) := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, sp2, rs2, g3, g4, o2, mem2⟩ := sha384Fn_correct m1 (by rw [hmem1]; exact C) hpc1
    (by rw [hr sp (by decide), hsp]) (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1])
    (by rw [hr a2 (by decide), ha2]) (by rw [hra]; exact even_clear _ (even_at base hb _ hev))
  rw [hmem1] at o2 mem2
  exact ⟨m2, c2, pc2.trans hra, ⟨o2, fun x h1 h2 => mem2 x h1.symm h2.symm⟩,
    tmc_keepPs [27] (ps := hfPs) (by decide) rs2 sp2 g3 g4⟩

/-- A call to `sha256(out, p, n)`. -/
theorem WP.callSha256M {hi lo out p sp0 : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 sha256FnAddress) (hev : (off + 8) % 2 = 0)
    (E : Sha256Env M out p sp0 n) (hsp : f sp = sp0) (h0 : f a0 = out) (ha1 : f a1 = p)
    (ha2 : f a2 = BitVec.ofNat 32 n) (hn : n < 2 ^ 31)
    (hSb : Sep (sp0 + 0xFFFFFD90) 0x270 base code.length) (hOb : Sep out 32 base code.length)
    (k : ∀ m2 : Machine, memBytes m2.mem out 32 = sha256 (memBytes M p n) →
      (∀ x, Sep x 1 (sp0 + 0xFFFFFD90) 0x270 → Sep x 1 out 32 → m2.mem x = M x) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := BitVec.ofNat 32 sha256FnAddress) (cl := jClob)
    (P := fun m2 => memBytes m2.mem out 32 = sha256 (memBytes M p n) ∧
      (∀ x, Sep x 1 (sp0 + 0xFFFFFD90) 0x270 → Sep x 1 out 32 → m2.mem x = M x))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => by rw [hP.2 _ (sep_pt hSb hi) (sep_pt hOb hi)]; exact hc i hi)
    (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  obtain ⟨m2, c2, pc2, sp2, rs2, o2, mem2⟩ := sha256Fn_correct m1 (by rw [hmem1]; exact E) hpc1
    (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1]) (by rw [hr a2 (by decide), ha2])
    (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev)) (by rw [hr sp (by decide), hsp]) hn
  rw [hmem1] at o2 mem2
  refine ⟨m2, c2, pc2, ⟨o2, fun x h1 h2 => mem2 x h1.symm h2.symm⟩, fun x hx => ?_⟩
  have hx' : x ∉ jClob := hx
  simp only [jClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
  obtain ⟨n10, n11, n12, n13, n14, n15, n16, n17, n5, n6, n7, n28, n29, n30, n31⟩ := hx'
  exact rs2 x n5 n6 n7 n10 n11 n12 n13 n14 n15 n16 n17 n28 n29 n30 n31

/-- What `ecdsa_signature` leaves at `out`: a zero byte and the scalars, or
a one byte and the error. -/
def tmcSigOut (N : Nat) (M M' : Word → BitVec 8) (out p : Word) (n : Nat) : Prop :=
  match ecdsaSigOf N M p n with
  | .ok (r, s) => M' out = 0 ∧
      (∀ j, j < N → M' (out + BitVec.ofNat 32 (1 + j)) = BitVec.ofNat 8 (r.getD j 0)) ∧
      ∀ j, j < N → M' (out + BitVec.ofNat 32 (N + 1 + j)) = BitVec.ofNat 8 (s.getD j 0)
  | .error b => M' out = 1 ∧ M' (out + 1) = b

/-- A call to `ecdsa_signature::<48>(out, p, n)`. -/
theorem WP.callEs48 {hi lo sp0 out p : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 ecdsaSignature48Address) (hev : (off + 8) % 2 = 0)
    (E : ESEnv M (BitVec.ofNat 32 ecdsaSignature48Address) sp0 out p n) (hsp : f sp = sp0) (h0 : f a0 = out)
    (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hSb : Sep (sp0 + 0xFFFFFE90) 0x170 base code.length) (hOb : Sep out 97 base code.length)
    (k : ∀ m2 : Machine, tmcSigOut 48 M m2.mem out p n →
      (∀ x, Sep x 1 (sp0 + 0xFFFFFE90) 0x170 → Sep x 1 out 97 → m2.mem x = M x) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := BitVec.ofNat 32 ecdsaSignature48Address) (cl := jClob)
    (P := fun m2 => tmcSigOut 48 M m2.mem out p n ∧
      (∀ x, Sep x 1 (sp0 + 0xFFFFFE90) 0x170 → Sep x 1 out 97 → m2.mem x = M x))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => by rw [hP.2 _ (sep_pt hSb hi) (sep_pt hOb hi)]; exact hc i hi)
    (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  obtain ⟨m2, c2, pc2, sp2, rs2, mem2, o2⟩ := ecdsaSignature48_correct m1 (by rw [hmem1]; exact E) hpc1
    (by rw [hr sp (by decide), hsp]) (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1])
    (by rw [hr a2 (by decide), ha2]) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
  rw [hmem1] at o2 mem2
  refine ⟨m2, c2, pc2, ⟨o2, fun x h1 h2 => mem2 x h1.symm h2.symm⟩, tmc_keepVal fun q hq => ?_⟩
  by_cases h2q : q = sp
  · subst h2q; rw [sp2, hr sp (by decide), hsp]
  · exact rs2 q (by revert hq h2q; revert q; decide)

/-- A call to `ecdsa_signature::<32>(out, p, n)`. -/
theorem WP.callEs32 {hi lo sp0 out p : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BitVec.ofNat 32 ecdsaSignature32Address) (hev : (off + 8) % 2 = 0)
    (E : ES32Env M (BitVec.ofNat 32 ecdsaSignature32Address) sp0 out p n) (hsp : f sp = sp0) (h0 : f a0 = out)
    (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hSb : Sep (sp0 + 0xFFFFFED0) 0x130 base code.length) (hOb : Sep out 65 base code.length)
    (k : ∀ m2 : Machine, tmcSigOut 32 M m2.mem out p n →
      (∀ x, Sep x 1 (sp0 + 0xFFFFFED0) 0x130 → Sep x 1 out 65 → m2.mem x = M x) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := BitVec.ofNat 32 ecdsaSignature32Address) (cl := jClob)
    (P := fun m2 => tmcSigOut 32 M m2.mem out p n ∧
      (∀ x, Sep x 1 (sp0 + 0xFFFFFED0) 0x130 → Sep x 1 out 65 → m2.mem x = M x))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => by rw [hP.2 _ (sep_pt hSb hi) (sep_pt hOb hi)]; exact hc i hi)
    (fun m2 hP => k m2 hP.1 hP.2)
  have hr := tmc_regs hreg1
  obtain ⟨m2, c2, pc2, sp2, rs2, mem2, o2⟩ := ecdsaSignature32_correct m1 (by rw [hmem1]; exact E) hpc1
    (by rw [hr sp (by decide), hsp]) (by rw [hr a0 (by decide), h0]) (by rw [hr a1 (by decide), ha1])
    (by rw [hr a2 (by decide), ha2]) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
  rw [hmem1] at o2 mem2
  refine ⟨m2, c2, pc2, ⟨o2, fun x h1 h2 => mem2 x h1.symm h2.symm⟩, tmc_keepVal fun q hq => ?_⟩
  by_cases h2q : q = sp
  · subst h2q; rw [sp2, hr sp (by decide), hsp]
  · exact rs2 q (by revert hq h2q; revert q; decide)

end

end C3.RV32
