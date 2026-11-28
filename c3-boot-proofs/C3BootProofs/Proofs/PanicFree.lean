import C3BootProofs.Proofs.P2vP256
import C3BootProofs.Proofs.Pv384Np
import C3BootProofs.Proofs.HaltCode

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

/-- **How the bootloader may stop**: at a deliberate `halt`, or in a panic
that only a failed inversion bound allows. -/
def HaltOut (m : Machine) : Prop := HaltsDeliberately m ∨ PanicIf m

theorem HaltOut.panics {m : Machine} (h : HaltOut m) : Panics m :=
  h.elim HaltsDeliberately.panics PanicIf.panics

theorem HaltOut.of_steps {m m' : Machine} (s : Steps m m') (h : HaltOut m') : HaltOut m :=
  h.imp (HaltsDeliberately.of_steps s) (PanicIf.of_steps s)

/-- Under `InvBounds`, the bootloader stops only at a deliberate `halt`. -/
theorem HaltOut.np {m : Machine} (hB : InvBounds) (h : HaltOut m) : HaltsDeliberately m :=
  h.elim id fun hp => (hp.absurd hB).elim

theorem HaltOut.deliberate {m : Machine} {c : Word} (hc : Deliberate c) (h : HaltsWith m c) : HaltOut m :=
  .inl ⟨c, hc, h⟩

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
