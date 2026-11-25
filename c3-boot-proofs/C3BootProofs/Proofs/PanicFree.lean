import C3BootProofs.Proofs.P2vP256
import C3BootProofs.Proofs.Pv384Np

/-!
# Panics that only a failed inversion bound allows

The image's only Rust panics that its proofs can't rule out come from the
two field inversions: `p256VerifyPrehash` and `p384VerifyPrehash` panic
only if safegcd's divstep bound fails for P-256 (`P2v.P256InvBound`) or
P-384 (`Pv.P384InvBound`). `InvBounds` is both bounds. Every other way the
bootloader stops is one of the deliberate `halt` calls in `boot_main` and
`boot`, with codes 0xE1 to 0xE5.

The theorems take no bound as a hypothesis. A conclusion that allowed a
panic instead says which panics it allows:

* `PanicIf m` is `¬ InvBounds ∧ Panics m`: the machine panics, and some
  inversion bound fails. `PanicIf.panics` weakens it to `Panics m`, and
  `PanicIf.absurd` refutes it under `InvBounds`.
* `HaltCode m c` says that `m` is entering the ROM's `printf` from `halt`,
  as `Halting m` says, with `halt`'s code `c` in `a1`. `rust_begin_unwind`
  passes `panicHaltCode`, 0xEF (`beginUnwind_haltCode`).
* `HaltOut m` is the outcome at the top: the machine halts with a
  deliberate code (`HaltsDeliberately m`), or `PanicIf m`. Under
  `InvBounds`, `HaltOut.np` leaves only the deliberate halt.

## Threading rule

A proof refines a panic disjunct as follows:

1. A callee's `… ∨ Panics m` becomes `… ∨ PanicIf m`. A stage that
   reaches `Halting n'` from such a call keeps `¬ InvBounds ∧ Halting n'`.
2. `PanicIf.of_steps` moves the refined disjunct back along `Steps`, as
   `Panics.of_steps` moves `Panics`.
3. A panic that another fact rules out, such as a bounds check that the
   proof shows can't fail, is refuted where it arises and never enters a
   disjunct.
4. A deliberate `halt` call gives `HaltsWith m c` with its code, from
   `halt_haltCode`. Only `boot_main` and `boot` call `halt` directly.
5. A theorem pinned in `Audit.lean` keeps its name and its statement,
   which follows from the refined one by `PanicIf.panics` or
   `HaltOut.panics`. The refined theorem has the suffix `_pi`, and the
   one that assumes `InvBounds` and has no panic disjunct has `_np`.
   Lemmas inside a proof family are refined in place.

`PanicFreeTargets.lean` states the refined contracts that the remaining
proofs establish, up to `reset_correct_loaded_pi` and
`reset_correct_loaded_np`.
-/

namespace C3.RV32

open C3.Image

/-- **Both inversion bounds**: safegcd's divstep bound holds for P-256's
and P-384's field inversions. -/
def InvBounds : Prop := P2v.P256InvBound ∧ Pv.P384InvBound

/-- The machine panics, and some inversion bound fails. -/
def PanicIf (m : Machine) : Prop := ¬ InvBounds ∧ Panics m

theorem PanicIf.panics {m : Machine} (h : PanicIf m) : Panics m := h.2

theorem PanicIf.absurd {m : Machine} (hB : InvBounds) (h : PanicIf m) : False := h.1 hB

theorem PanicIf.of_steps {m m' : Machine} (c : Steps m m') (h : PanicIf m') : PanicIf m :=
  ⟨h.1, h.2.of_steps c⟩

/-- The machine is entering the ROM's `printf` from `halt` with `halt`'s
code `c`, which `halt` moved to `a1`. -/
def HaltCode (m : Machine) (c : Word) : Prop := Halting m ∧ reg m a1 = c

/-- The codes of the deliberate `halt` calls: 0xE1 to 0xE5. -/
def deliberateCodes : List Word := [0xE1, 0xE2, 0xE3, 0xE4, 0xE5]

/-- `c` is the code of a deliberate `halt` call. -/
def Deliberate (c : Word) : Prop := c ∈ deliberateCodes

/-- The code that `rust_begin_unwind` passes to `halt`. -/
def panicHaltCode : Word := 0xEF

theorem panicHaltCode_not_deliberate : ¬ Deliberate panicHaltCode :=
  show panicHaltCode ∉ deliberateCodes by decide

/-- From `m`, the machine reaches `halt`'s ROM call with code `c`. -/
def HaltsWith (m : Machine) (c : Word) : Prop := ∃ m', Steps m m' ∧ HaltCode m' c

/-- From `m`, the machine reaches `halt`'s ROM call with a deliberate code. -/
def HaltsDeliberately (m : Machine) : Prop := ∃ c, Deliberate c ∧ HaltsWith m c

/-- **How the bootloader may stop**: at a deliberate `halt`, or in a panic
that only a failed inversion bound allows. -/
def HaltOut (m : Machine) : Prop := HaltsDeliberately m ∨ PanicIf m

theorem HaltsWith.panics {m : Machine} {c : Word} (h : HaltsWith m c) : Panics m :=
  let ⟨m', s, hh, _⟩ := h; ⟨m', s, hh⟩

theorem HaltsWith.of_steps {m m' : Machine} {c : Word} (s : Steps m m') (h : HaltsWith m' c) : HaltsWith m c :=
  let ⟨m'', s', hh⟩ := h; ⟨m'', s.trans s', hh⟩

theorem HaltsDeliberately.panics {m : Machine} (h : HaltsDeliberately m) : Panics m :=
  let ⟨_, _, hw⟩ := h; hw.panics

theorem HaltsDeliberately.of_steps {m m' : Machine} (s : Steps m m') (h : HaltsDeliberately m') :
    HaltsDeliberately m :=
  let ⟨c, hc, hw⟩ := h; ⟨c, hc, hw.of_steps s⟩

theorem HaltOut.panics {m : Machine} (h : HaltOut m) : Panics m :=
  h.elim HaltsDeliberately.panics PanicIf.panics

theorem HaltOut.of_steps {m m' : Machine} (s : Steps m m') (h : HaltOut m') : HaltOut m :=
  h.imp (HaltsDeliberately.of_steps s) (PanicIf.of_steps s)

/-- Under `InvBounds`, the bootloader stops only at a deliberate `halt`. -/
theorem HaltOut.np {m : Machine} (hB : InvBounds) (h : HaltOut m) : HaltsDeliberately m :=
  h.elim id fun hp => (hp.absurd hB).elim

theorem HaltOut.deliberate {m : Machine} {c : Word} (hc : Deliberate c) (h : HaltsWith m c) : HaltOut m :=
  .inl ⟨c, hc, h⟩

set_option maxRecDepth 20000 in
/-- **`halt`** with its code `reg m a0` reaches the ROM's `printf` with that
code in `a1`. -/
theorem halt_haltCode (m : Machine) (hP : PanicCode m.mem) (hpc : m.pc = haltBase)
    (hR : Room (reg m sp) 16) : HaltsWith m (reg m a0) := by
  have hc := haltCode_in hP
  have st0 : St m.mem haltBase m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hR
  obtain ⟨mA, cA, uA⟩ := St.block hltA st0 hc hltA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, hltA, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hS]
    repeat' apply And.intro
    all_goals first | exact True.intro | (refine aligned_add (aligned_add hR.1 ?_) ?_ <;> decide) |
      exact hR.sep (o := 0xC) (by decide) (by decide) (by decide) (by decide))
  simp only [runBlock, BInstr.run, hltA] at uA
  have hPA : PanicCode mA.mem := by
    rw [uA.mem]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS]
    exact hP.store32 (hR.slot (o := 0xC) (by decide) (by decide))
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := uA.self.callRa (by rw [← uA.mem]; exact haltCode_in hPA) hlt_at_e hlt_at_12
    (cb := romPrintfEntry) (by decide) (by decide)
  refine ⟨n1, cA.trans c1, ⟨pc1, ?_, by rw [mem1, ← uA.mem]; exact hPA⟩, ?_⟩
  · rw [regs1]; simp +decide only [upd_app, ↓reduceIte]
  · rw [regs1, upd_ne (by decide) (by decide), uA.regs]; simp +decide only [upd_app, ↓reduceIte]
    simp only [aluEval]; exact BitVec.zero_add _

/-- **`rust_begin_unwind`** reaches the ROM's `printf` from `halt` with code
0xEF. -/
theorem beginUnwind_haltCode (m : Machine) (hP : PanicCode m.mem) (hpc : m.pc = BitVec.ofNat 32 beginUnwindAddress)
    (hR : Room (reg m sp) 16) : HaltsWith m panicHaltCode := by
  have hc := unwindCode_in hP
  have st0 : St m.mem (BitVec.ofNat 32 beginUnwindAddress) m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨m1, e1, s1⟩ := st0.aluImm hc unw_at_0 (off' := 4) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s1.self.callRa hc unw_at_4 unw_at_8 (cb := haltBase) (by decide)
    (by decide)
  have h := halt_haltCode n1 (by rw [mem1]; exact hP) pc1 (by
    rw [regs1, upd_ne (by decide) (by decide), s1.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact hR)
  have e : reg n1 a0 = panicHaltCode := by
    rw [regs1, upd_ne (by decide) (by decide), s1.regs]
    simp +decide only [upd_app, ↓reduceIte]; rfl
  rw [e] at h
  exact h.of_steps (.cons e1 c1)

end C3.RV32

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv C3.RV32.Gd

/-- **`p256VerifyPrehash`**, from its entry to its return: it panics only
if an inversion bound fails, returns 0, or returns 1 with `SvP256Facts` for
the key at `pk`, the digest at `dg`, and the scalars at `rp` and `sq`. It
returns with `sp`, `ra`, `s0` to `s11`, `gp`, and `tp` as they were, and
changes no memory outside its frame. -/
theorem p256VerifyPrehash_correct_pi (m : Machine) {B pk dg rp sq : Word}
    (E : P2vEnv m.mem) (F : Fr B 0x3590) (hpc : m.pc = P2V) (hsp : reg m sp = B + 0x3590)
    (ha0 : reg m a0 = pk) (ha1 : reg m a1 = dg) (ha2 : reg m a2 = rp) (ha3 : reg m a3 = sq)
    (hret : reg m ra &&& ~~~1 = reg m ra) (RS : P2vRoSep B)
    (r_in : P2vIn B rp 32) (s_in : P2vIn B sq 32) (k_in : P2vIn B pk 0x41) (dg_in : P2vIn B dg 32) :
    PanicIf m ∨ P2vRet B (fun k => reg m (savedReg k)) m 0 ∨
    (SvP256Facts m.mem pk dg (memBytes m.mem rp 32) (memBytes m.mem sq 32) ∧
      P2vRet B (fun k => reg m (savedReg k)) m 1) := by
  rcases p256VerifyPrehash_correct_bound m E F hpc hsp ha0 ha1 ha2 ha3 hret RS r_in s_in k_in dg_in with
    ⟨h, hp⟩ | h
  · have z := code_accV E.UD 0 8 (by decide)
    rw [add_ofNat_zero] at z
    exact .inl ⟨fun hB => h hB.1 (z.trans (by decide)), hp⟩
  · exact .inr h

/-- **`p256VerifyPrehash`**, from its entry to its return: it panics,
returns 0, or returns 1 with `SvP256Facts` for the key at `pk`, the digest
at `dg`, and the scalars at `rp` and `sq`. It returns with `sp`, `ra`, `s0`
to `s11`, `gp`, and `tp` as they were, and changes no memory outside its
frame. -/
theorem p256VerifyPrehash_correct (m : Machine) {B pk dg rp sq : Word}
    (E : P2vEnv m.mem) (F : Fr B 0x3590) (hpc : m.pc = P2V) (hsp : reg m sp = B + 0x3590)
    (ha0 : reg m a0 = pk) (ha1 : reg m a1 = dg) (ha2 : reg m a2 = rp) (ha3 : reg m a3 = sq)
    (hret : reg m ra &&& ~~~1 = reg m ra) (RS : P2vRoSep B)
    (r_in : P2vIn B rp 32) (s_in : P2vIn B sq 32) (k_in : P2vIn B pk 0x41) (dg_in : P2vIn B dg 32) :
    Panics m ∨ P2vRet B (fun k => reg m (savedReg k)) m 0 ∨
    (SvP256Facts m.mem pk dg (memBytes m.mem rp 32) (memBytes m.mem sq 32) ∧
      P2vRet B (fun k => reg m (savedReg k)) m 1) :=
  (p256VerifyPrehash_correct_pi m E F hpc hsp ha0 ha1 ha2 ha3 hret RS r_in s_in k_in dg_in).imp_left
    PanicIf.panics

end C3.RV32.P2v

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

/-- If `pvModel` is `none`, some inversion bound fails. -/
theorem pvModel_none_inv {M : Word → BitVec 8} {pk ph : Word} {len : Nat} {rp sp' : Word}
    (h : pvModel M pk ph len rp sp' = none) : ¬ InvBounds := fun hB => by
  obtain ⟨v, hv⟩ := pvnp_model hB.2 M pk ph len rp sp'
  rw [h] at hv
  cases hv

/-- **`p384VerifyPrehash`**, from its entry to its return: it panics only
if an inversion bound fails, or it returns `pvModel` of the inputs. It
returns with `sp`, `ra`, `s0` to `s11`, `gp`, and `tp` as they were, and
changes no memory outside its frame. -/
theorem p384VerifyPrehash_correct_pi (m : Machine) {B pk ph rp sp' retAddr : Word} {len : Nat}
    (E : PvEnv7 m.mem) (F : Fr B 0x21A0) (hpc : m.pc = PV) (hsp : reg m sp = B + 0x21A0)
    (ha0 : reg m a0 = pk) (ha1 : reg m a1 = ph) (ha2 : reg m a2 = BitVec.ofNat 32 len) (ha3 : reg m a3 = rp)
    (ha4 : reg m a4 = sp') (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (sPK : Sep pk 0x61 (B + 0xFFFFFE60) 0x2340) (hPK : pk.toNat + 0x61 ≤ 0x40000000)
    (sR : Sep rp 48 (B + 0xFFFFFE60) 0x2340) (sS : Sep sp' 48 (B + 0xFFFFFE60) 0x2340)
    (sph : Sep ph len (B + 0xFFFFFE60) 0x2340) (hph : ph.toNat + len < 2 ^ 32) :
    PanicIf m ∨
    (∃ v, pvModel m.mem pk ph len rp sp' = some v ∧
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = B + 0x21A0 ∧
        (∀ k, k < 13 → reg m' (savedReg k) = reg m (savedReg k)) ∧
        reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧ reg m' a0 = v ∧
        PvOut B m.mem m'.mem) :=
  (p384VerifyPrehash_correct m E F hpc hsp ha0 ha1 ha2 ha3 ha4 hra hret sPK hPK sR sS sph hph
    (C3.RV32.Safegcd.pvSide_holds _ _ _ _ _ _)).imp_left fun ⟨hn, hp⟩ => ⟨pvModel_none_inv hn, hp⟩

end C3.RV32.Pv
