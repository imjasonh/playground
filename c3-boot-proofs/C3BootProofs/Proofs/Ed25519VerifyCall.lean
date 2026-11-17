import C3BootProofs.Proofs.EdvReduceBody
import C3BootProofs.Proofs.Ed25519PkOk

/-!
# `c3_crypto::ed25519_verify`: frame, invariant, prologue, and epilogue

`ed25519_verify(pk, msg, sig)` keeps a 0x16A0-byte frame at `F` and calls
functions whose own frames reach 0xA10 bytes below it, so the stack it may
write is the 0x20B0 bytes at `G = F - 0xA10`. Between calls the state is
`EvSt`: `sp` at `F`, `gp` and `tp` as on entry, memory outside the stack as
on entry, and the slots of the thirteen registers the prologue saves as
after the prologue. `EvSt.ret` re-establishes it after a call that wrote
only below `F` and to one range of the frame.
-/

namespace C3.RV32

open C3.Image

abbrev EV : Word := BitVec.ofNat 32 ed25519VerifyAddress

/-- The base of the stack `ed25519_verify` and its callees write. -/
abbrev evG (F : Word) : Word := F + 0xFFFFF5F0

set_option maxRecDepth 20000 in
/-- A `PkEnv` survives any change below the code that keeps `ONE`. -/
theorem PkEnv.hi {M M' : Word → BitVec 8} (E : PkEnv M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x)
    (ho : feW M' (BitVec.ofNat 32 edOneAddress) = feW M (BitVec.ofNat 32 edOneAddress)) : PkEnv M' :=
  ⟨E.dec.hi h, E.iso.hi h ho, E.vkb.hi h (by decide) (by decide), E.pko.hi h (by decide) (by decide),
    E.ltl.hi h (by decide) (by decide), E.aeq.hi h (by decide) (by decide), E.mcmp.hi h (by decide) (by decide)⟩

/-- The code `ed25519_verify` runs and its callees'. -/
structure EvEnv (M : Word → BitVec 8) : Prop where
  pk : PkEnv M
  cod : CodeIn M EV ed25519VerifyCode
  s29s : CodeIn M (BitVec.ofNat 32 scalar29SubAddress) scalar29SubCode
  s29i : CodeIn M (BitVec.ofNat 32 scalar29IndexAddress) scalar29IndexCode
  s29im : CodeIn M (BitVec.ofNat 32 scalar29IndexMutAddress) scalar29IndexMutCode
  sL : CodeIn M (BitVec.ofNat 32 scalarLAddress) scalarLData
  s29p : CodeIn M (BitVec.ofNat 32 scalar29PackAddress) scalar29PackCode

/-- Where `ed25519_verify` runs: its frame at `F`, 16-aligned, with the
0xA10 bytes below it, all below the code and apart from the read-only data
at `0x3FCC4000`, and the key `pk`, the signature `sig`, and the `len`
bytes of message at `msg`, each apart from that stack. -/
structure EvCtx (M0 : Word → BitVec 8) (F pk sig msg : Word) (len : Nat) : Prop where
  env : EvEnv M0
  hF : F.toNat % 16 = 0
  hlo : 0xA10 ≤ F.toNat
  hhi : F.toNat + 0x16A0 ≤ 0x40000000
  sRo : Sep (BitVec.ofNat 32 0x3FCC4000) 0x1400 (evG F) 0x20B0
  sPk : Sep pk 32 (evG F) 0x20B0
  sSig : Sep sig 64 (evG F) 0x20B0
  sMsg : Sep msg len (evG F) 0x20B0
  hpk : pk.toNat + 32 < 2 ^ 32
  hsig : sig.toNat + 64 < 2 ^ 32
  hmsg : msg.toNat + len ≤ 2 ^ 32

/-- Between calls: `sp` at `F`, `gp` and `tp` as in `r0`, memory outside
the stack as `M0`, and the saved registers' slots as `Ms`. -/
structure EvSt (M0 Ms : Word → BitVec 8) (F : Word) (r0 : Fin 32 → Word) (M : Word → BitVec 8) (n : Machine)
    (off : Nat) : Prop where
  st : St M EV n off (reg n)
  hsp : reg n sp = F
  gp : reg n 3 = r0 3
  tp : reg n 4 = r0 4
  agree : ∀ x, Sep (evG F) 0x20B0 x 1 → M x = M0 x
  slots : ∀ c, 0x166C ≤ c → c < 0x16A0 → M (F + BitVec.ofNat 32 c) = Ms (F + BitVec.ofNat 32 c)

theorem ev_len : ed25519VerifyCode.length = 6612 := by decide +kernel

section Ctx
variable {M0 : Word → BitVec 8} {F pk sig msg : Word} {len : Nat}

theorem evF_G (F : Word) (c : Nat) : F + BitVec.ofNat 32 c = evG F + BitVec.ofNat 32 (0xA10 + c) := by
  rw [evG, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFF5F0 : Word).toNat = 2 ^ 32 - 0xA10 from rfl]
  omega

theorem evZ_G (F z : Word) {S : Nat} (hz : z.toNat = 2 ^ 32 - S) (hS : S ≤ 0xA10) :
    F + z = evG F + BitVec.ofNat 32 (0xA10 - S) := by
  rw [evG, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hz, show (0xFFFFF5F0 : Word).toNat = 2 ^ 32 - 0xA10 from rfl]
  omega

theorem add_spm (R : Word) {a b c : Nat} (h : (a + b) % 2 ^ 32 = c) :
    aluEval .add (R + BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = R + BitVec.ofNat 32 c := by
  rw [add_sp R rfl]; congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, ← h, Nat.mod_mod]

theorem EvCtx.gN (C : EvCtx M0 F pk sig msg len) : (evG F).toNat = F.toNat - 0xA10 := by
  have := C.hlo
  rw [evG, BitVec.toNat_add, show (0xFFFFF5F0 : Word).toNat = 2 ^ 32 - 0xA10 from rfl]; omega

theorem EvCtx.fN (C : EvCtx M0 F pk sig msg len) {c : Nat} (h : c ≤ 0x16A0) :
    (F + BitVec.ofNat 32 c).toNat = F.toNat + c := by
  have := C.hhi; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem EvCtx.al (C : EvCtx M0 F pk sig msg len) {c : Nat} (h : c % 4 = 0) : (F + BitVec.ofNat 32 c).toNat % 4 = 0 :=
  aligned_add (by have := C.hF; omega) h

theorem EvCtx.offs (_ : EvCtx M0 F pk sig msg len) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 0x16A0)
    (hd : d + k ≤ 0x16A0) : Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 d) k :=
  sep_offsets F h (by omega) (by omega)

theorem EvCtx.inG (_ : EvCtx M0 F pk sig msg len) {c l : Nat} (h : c + l ≤ 0x16A0) {x : Word}
    (hx : Sep (evG F) 0x20B0 x 1) : Sep (F + BitVec.ofNat 32 c) l x 1 := by
  rw [evF_G]; exact (hx.symm.subR (by omega)).symm

/-- The callees' stack is apart from the frame. -/
theorem EvCtx.zF (_ : EvCtx M0 F pk sig msg len) {c l : Nat} (h : c + l ≤ 0x16A0) :
    Sep (evG F) 0xA10 (F + BitVec.ofNat 32 c) l := by
  rw [evF_G]
  have := sep_offsets (evG F) (c := 0) (n := 0xA10) (d := 0xA10 + c) (k := l) (Or.inl (by omega)) (by omega) (by omega)
  rwa [add_ofNat_zero] at this

theorem EvCtx.zG (_ : EvCtx M0 F pk sig msg len) {x : Word} (hx : Sep (evG F) 0x20B0 x 1) : Sep (evG F) 0xA10 x 1 := by
  have := hx.sub (c := 0) (l := 0xA10) (by omega); rwa [add_ofNat_zero] at this

theorem EvCtx.hiG (C : EvCtx M0 F pk sig msg len) {b : Word} {k : Nat} (h1 : 0x40000000 ≤ b.toNat)
    (h2 : b.toNat + k ≤ 2 ^ 32) : Sep (evG F) 0x20B0 b k :=
  sep_of_le (by rw [C.gN]; have := C.hhi; omega) h2

/-- A read-only datum is apart from the stack. -/
theorem EvCtx.ro (C : EvCtx M0 F pk sig msg len) {a k : Nat} (h1 : 0x3FCC4000 ≤ a) (h2 : a + k ≤ 0x3FCC5400) :
    Sep (BitVec.ofNat 32 a) k (evG F) 0x20B0 := by
  have := C.sRo.sub (c := a - 0x3FCC4000) (l := k) (by omega)
  rwa [BitVec.ofNat_add_ofNat, show 0x3FCC4000 + (a - 0x3FCC4000) = a by omega] at this

/-- A range apart from the stack is apart from a callee's frame of `S`
bytes below `F`. -/
theorem EvCtx.zone (_ : EvCtx M0 F pk sig msg len) {x z : Word} {k S : Nat} (hz : z.toNat = 2 ^ 32 - S)
    (hS : S ≤ 0xA10) (h : Sep x k (evG F) 0x20B0) : Sep x k (F + z) S := by
  have e := evZ_G F z hz hS
  rw [e]; exact h.subR (by omega)

/-- The frame is apart from a callee's frame below `F`. -/
theorem EvCtx.zoneF (_ : EvCtx M0 F pk sig msg len) {z : Word} {c l S : Nat} (hz : z.toNat = 2 ^ 32 - S)
    (hS : S ≤ 0xA10) (h : c + l ≤ 0x16A0) : Sep (F + BitVec.ofNat 32 c) l (F + z) S := by
  have e := evZ_G F z hz hS
  rw [e, evF_G]; exact sep_offsets (evG F) (Or.inr (by omega)) (by omega) (by omega)

/-- Memory a callee with a frame of `S` bytes below `F` may write lies in
the callees' stack. -/
theorem EvCtx.zoneIn (_ : EvCtx M0 F pk sig msg len) {x z : Word} {S : Nat} (hz : z.toNat = 2 ^ 32 - S)
    (hS : S ≤ 0xA10) (h : Sep (evG F) 0xA10 x 1) : Sep (F + z) S x 1 := by
  rw [evZ_G F z hz hS]; exact h.sub (by omega)

theorem EvCtx.codeF (C : EvCtx M0 F pk sig msg len) {c l : Nat} (h : c + l ≤ 0x16A0) {b : Word} {k : Nat}
    (h1 : 0x40000000 ≤ b.toNat) (h2 : b.toNat + k ≤ 2 ^ 32) : Sep (F + BitVec.ofNat 32 c) l b k :=
  sep_of_le (by rw [C.fN (by omega)]; have := C.hhi; omega) h2

end Ctx

section St
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word} {M : Word → BitVec 8}
  {n : Machine} {off : Nat}

theorem EvSt.hiM (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) :
    ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x :=
  fun x hx => D.agree x (C.hiG hx (by have := x.isLt; omega))

theorem EvSt.roM (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {a k : Nat} (h1 : 0x3FCC4000 ≤ a)
    (h2 : a + k ≤ 0x3FCC5400) : ∀ i, i < k → M (BitVec.ofNat 32 a + BitVec.ofNat 32 i) = M0 (BitVec.ofNat 32 a + BitVec.ofNat 32 i) :=
  fun i hi => D.agree _ ((C.ro h1 h2).sub (c := i) (l := 1) (by omega)).symm

theorem EvSt.feRo (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {a : Nat} (h1 : 0x3FCC4000 ≤ a)
    (h2 : a + 40 ≤ 0x3FCC5400) : feW M (BitVec.ofNat 32 a) = feW M0 (BitVec.ofNat 32 a) :=
  feW_frame fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact D.agree _ ((C.ro h1 h2).sub (c := 4 * i + j) (l := 1) (by omega)).symm

theorem EvSt.bytesRo (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {a k : Nat} (h1 : 0x3FCC4000 ≤ a)
    (h2 : a + k ≤ 0x3FCC5400) : memBytes M (BitVec.ofNat 32 a) k = memBytes M0 (BitVec.ofNat 32 a) k :=
  memBytes_congr fun i hi => D.roM C h1 h2 i hi

theorem EvSt.bytesOut (D : EvSt M0 Ms F r0 M n off) {p : Word} {k : Nat} (h : Sep p k (evG F) 0x20B0) :
    memBytes M p k = memBytes M0 p k :=
  memBytes_congr fun i hi => D.agree _ (h.sub (c := i) (l := 1) hi).symm

theorem EvSt.code (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) : CodeIn M EV ed25519VerifyCode :=
  C.env.cod.hi (D.hiM C) (by decide) (by rw [ev_len]; decide)

theorem EvSt.codeRo (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {a : Nat} {code : List Nat}
    (h : CodeIn M0 (BitVec.ofNat 32 a) code) (h1 : 0x3FCC4000 ≤ a) (h2 : a + code.length ≤ 0x3FCC5400) :
    CodeIn M (BitVec.ofNat 32 a) code :=
  fun i hi => by rw [D.roM C h1 h2 i hi]; exact h i hi

theorem EvSt.pkEnv (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) : PkEnv M :=
  C.env.pk.hi (D.hiM C) (D.feRo C (by decide) (by decide))

theorem EvSt.jmp (D : EvSt M0 Ms F r0 M n off) {n1 : Machine} {off' : Nat} (u : St M EV n1 off' (reg n)) :
    EvSt M0 Ms F r0 M n1 off' :=
  ⟨u.self, by rw [u.regs, D.hsp], by rw [u.regs, D.gp], by rw [u.regs, D.tp], D.agree, D.slots⟩

/-- After straight-line code that changed registers other than `sp`, `gp`,
and `tp` and kept memory. -/
theorem EvSt.regs (D : EvSt M0 Ms F r0 M n off) {n1 : Machine} {off' : Nat} (u : St M EV n1 off' (reg n1))
    (h : ∀ q, q = sp ∨ q = (3 : Fin 32) ∨ q = (4 : Fin 32) → reg n1 q = reg n q) : EvSt M0 Ms F r0 M n1 off' :=
  ⟨u, by rw [h sp (Or.inl rfl), D.hsp], by rw [h 3 (Or.inr (Or.inl rfl)), D.gp],
    by rw [h 4 (Or.inr (Or.inr rfl)), D.tp], D.agree, D.slots⟩

/-- After a call that returned to `off'` with `sp`, `gp`, and `tp` kept,
having written only the callees' stack below `F` and the `k` bytes at
`F + d`, below the slots. -/
theorem EvSt.ret (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {n' : Machine} {d k off' : Nat}
    (hpc : n'.pc = EV + BitVec.ofNat 32 off') (hsp : reg n' sp = F) (h3 : reg n' 3 = reg n 3)
    (h4 : reg n' 4 = reg n 4) (hd : d + k ≤ 0x166C)
    (hfr : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 d) k x 1 → n'.mem x = M x) :
    EvSt M0 Ms F r0 n'.mem n' off' :=
  ⟨⟨hpc, rfl, fun _ => rfl⟩, hsp, by rw [h3, D.gp], by rw [h4, D.tp],
    fun x hx => by rw [hfr x (C.zG hx) (C.inG (by omega) hx), D.agree x hx],
    fun c h1 h2 => by
      rw [hfr _ (C.zF (by omega)) (C.offs (Or.inl (by omega)) (by omega) (by omega)), D.slots c h1 h2]⟩

/-- After a store of `k` bytes at `F + d`, below the slots. -/
theorem EvSt.store (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {M' : Word → BitVec 8} {n1 : Machine}
    {d k off' : Nat} (u : St M' EV n1 off' (reg n1)) (hsp : reg n1 sp = F) (h3 : reg n1 3 = reg n 3)
    (h4 : reg n1 4 = reg n 4) (hd : d + k ≤ 0x166C)
    (hfr : ∀ x, Sep (F + BitVec.ofNat 32 d) k x 1 → M' x = M x) : EvSt M0 Ms F r0 M' n1 off' :=
  ⟨u, hsp, by rw [h3, D.gp], by rw [h4, D.tp],
    fun x hx => by rw [hfr x (C.inG (by omega) hx), D.agree x hx],
    fun c h1 h2 => by rw [hfr _ (C.offs (Or.inl (by omega)) (by omega) (by omega)), D.slots c h1 h2]⟩

/-- A block of register operations that leaves `sp`, `gp`, `tp`, and
memory alone. -/
theorem EvSt.block (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) (blk : List BInstr) {off' : Nat}
    (he : blockEnd ed25519VerifyCode off blk = some off')
    (hok : BlockOk EV ed25519VerifyCode.length blk (M, reg n)) (hm : (runBlock blk (M, reg n)).1 = M)
    (hk : ∀ q : Fin 32, q = sp ∨ q = (3 : Fin 32) ∨ q = (4 : Fin 32) → (runBlock blk (M, reg n)).2 q = reg n q) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 M n' off' ∧ ∀ q, reg n' q = (runBlock blk (M, reg n)).2 q := by
  obtain ⟨n', c, u⟩ := St.block blk D.st (D.code C) he hok
  rw [hm] at u
  exact ⟨n', c, D.regs ⟨u.pc, u.mem, fun _ => rfl⟩ (fun q hq => by rw [u.regs]; exact hk q hq), u.regs⟩

/-- A word store into the frame below the slots. -/
theorem EvSt.sw (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {rs1 rs2 : Fin 32} {imm len' : Word}
    {off' c : Nat} (hf : fetchRel ed25519VerifyCode off = some (.store .sw rs1 rs2 imm, len'))
    (hn : BitVec.ofNat 32 off + len' = BitVec.ofNat 32 off') (ha : reg n rs1 + imm = F + BitVec.ofNat 32 c)
    (hc4 : c % 4 = 0) (hc : c + 4 ≤ 0x166C) :
    ∃ n1, step n = some n1 ∧ EvSt M0 Ms F r0 (memStore32 M (F + BitVec.ofNat 32 c) (reg n rs2)) n1 off' ∧
      ∀ q, reg n1 q = reg n q := by
  obtain ⟨n1, d1, u1⟩ := D.st.sw (D.code C) hf hn (by rw [ha]; exact C.al hc4)
  rw [ha] at u1
  exact ⟨n1, d1, D.store C (d := c) (k := 4) u1.self (by rw [u1.regs, D.hsp]) (by rw [u1.regs]) (by rw [u1.regs]) hc
    (fun x hx => st32_frame hx), u1.regs⟩

/-- `beqz a0` on a flag `c`: on to `off'` when it is set, to `offT` when
it is clear. -/
theorem EvSt.br0 (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n off) {o : Word} {offT off' : Nat}
    (hf : fetchRel ed25519VerifyCode off = some (.branch .beq a0 x0 o, 4))
    (hT : BitVec.ofNat 32 off + o = BitVec.ofNat 32 offT) (hn : off + 4 = off') {c : Bool}
    (ha : reg n a0 = if c then 1 else 0) :
    ∃ n', Steps n n' ∧ (∀ q, reg n' q = reg n q) ∧ (c = true → EvSt M0 Ms F r0 M n' off') ∧
      (c = false → EvSt M0 Ms F r0 M n' offT) := by
  have s := D.st
  cases c with
  | false =>
    obtain ⟨n1, d1, u1⟩ := s.taken (D.code C) offT hf hT (by rw [ha, s.zero]; rfl)
    exact ⟨n1, .single d1, u1.regs, fun h => Bool.noConfusion h, fun _ => D.jmp u1⟩
  | true =>
    obtain ⟨n1, d1, u1⟩ := s.notTaken (D.code C) off' hf
      (by rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, BitVec.ofNat_add_ofNat, hn]) (by rw [ha, s.zero]; rfl)
    exact ⟨n1, .single d1, u1.regs, fun _ => D.jmp u1, fun h => Bool.noConfusion h⟩

end St

/-! ## Prologue and epilogue -/

theorem blockEnd_cons' {code : List Nat} {off off' : Nat} {i : BInstr} {is : List BInstr} {l : Word}
    {r : Option Nat} (h : fetchRel code off = some (i.toInstr, l)) (hn : off + l.toNat = off')
    (hr : blockEnd code off' is = r) : blockEnd code off (i :: is) = r := by
  subst hn; unfold blockEnd; rw [h]; exact (ite_eq_left rfl).trans hr

/-- The registers the prologue saves, at their offsets from `F + 0x1630`. -/
abbrev evPs : List (Fin 32 × Word) :=
  [(ra, BitVec.ofNat 32 0x6C), ((8 : Fin 32), BitVec.ofNat 32 0x68), ((9 : Fin 32), BitVec.ofNat 32 0x64), ((18 : Fin 32), BitVec.ofNat 32 0x60), ((19 : Fin 32), BitVec.ofNat 32 0x5C), ((20 : Fin 32), BitVec.ofNat 32 0x58), ((21 : Fin 32), BitVec.ofNat 32 0x54), ((22 : Fin 32), BitVec.ofNat 32 0x50), ((23 : Fin 32), BitVec.ofNat 32 0x4C), ((24 : Fin 32), BitVec.ofNat 32 0x48), ((25 : Fin 32), BitVec.ofNat 32 0x44), ((26 : Fin 32), BitVec.ofNat 32 0x40), ((27 : Fin 32), BitVec.ofNat 32 0x3C)]

section
set_option maxRecDepth 20000
theorem evSave_end : blockEnd ed25519VerifyCode 0x8 (saveBlockR a4 evPs) = some 0x38 :=
  blockEnd_cons' ev_at_8 rfl (blockEnd_cons' ev_at_c rfl (blockEnd_cons' ev_at_e rfl (blockEnd_cons' ev_at_10 rfl (blockEnd_cons' ev_at_14 rfl (blockEnd_cons' ev_at_18 rfl (blockEnd_cons' ev_at_1c rfl (blockEnd_cons' ev_at_20 rfl (blockEnd_cons' ev_at_24 rfl (blockEnd_cons' ev_at_28 rfl (blockEnd_cons' ev_at_2c rfl (blockEnd_cons' ev_at_30 rfl (blockEnd_cons' ev_at_34 rfl (rfl)))))))))))))
theorem evRestore_end : blockEnd ed25519VerifyCode 0x1016 (restoreBlockR a1 evPs) = some 0x1046 :=
  blockEnd_cons' ev_at_1016 rfl (blockEnd_cons' ev_at_101a rfl (blockEnd_cons' ev_at_101c rfl (blockEnd_cons' ev_at_101e rfl (blockEnd_cons' ev_at_1022 rfl (blockEnd_cons' ev_at_1026 rfl (blockEnd_cons' ev_at_102a rfl (blockEnd_cons' ev_at_102e rfl (blockEnd_cons' ev_at_1032 rfl (blockEnd_cons' ev_at_1036 rfl (blockEnd_cons' ev_at_103a rfl (blockEnd_cons' ev_at_103e rfl (blockEnd_cons' ev_at_1042 rfl (rfl)))))))))))))
theorem evPs_range : ∀ p ∈ evPs, p.2.toNat % 4 = 0 ∧ 0x3C ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x70 := by decide
theorem evPs_sp : ∀ p ∈ evPs, p.1 ≠ sp := by decide
theorem evPs_a1 : ∀ p ∈ evPs, p.1 ≠ a1 := by decide
end


theorem evSl (F o : Word) (_ : o.toNat < 0x70) : F + BitVec.ofNat 32 0x1630 + o = F + BitVec.ofNat 32 (0x1630 + o.toNat) := by
  rw [BitVec.add_assoc]; congr 1

theorem evPs_mem {r : Fin 32} {o : Word} (h : (r, o) ∈ evPs) :
    r ≠ sp ∧ r ≠ a4 ∧ r ≠ a1 ∧ r.val ≠ 0 ∧ o.toNat % 4 = 0 ∧ 0x3C ≤ o.toNat ∧ o.toNat + 4 ≤ 0x70 := by
  simp only [evPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem evPs_slot {r : Fin 32} {o : Word} (h : (r, o) ∈ evPs) :
    ∀ p ∈ evPs, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
      p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32) := by
  simp only [evPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem evPs_restore (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) :
    ∀ r o, (r, o) ∈ evPs → restoreRegs M G f evPs r = memLoad32 M (G + o) := by
  intro r o hm
  simp only [evPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp +decide only [restoreRegs, upd, ↓reduceIte]

theorem EvSt.slotW {M0 Ms : Word → BitVec 8} {F : Word} {r0 : Fin 32 → Word} {M : Word → BitVec 8} {n : Machine}
    {off : Nat} (D : EvSt M0 Ms F r0 M n off) {c : Nat} (h1 : 0x166C ≤ c) (h2 : c + 4 ≤ 0x16A0) :
    memLoad32 M (F + BitVec.ofNat 32 c) = memLoad32 Ms (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact D.slots _ (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From the entry to offset 0x40: the thirteen registers saved at
`F + 0x1630` and `sp` at `F`. -/
theorem ev_pro (m : Machine) {F pk sig msg : Word} {len : Nat} (C : EvCtx m.mem F pk sig msg len) (hpc : m.pc = EV)
    (hsp : reg m sp = F + BitVec.ofNat 32 0x16A0) :
    ∃ n Ms, Steps m n ∧ EvSt m.mem Ms F (reg m) Ms n 0x40 ∧
      (∀ r o, (r, o) ∈ evPs → memLoad32 Ms (F + BitVec.ofNat 32 0x1630 + o) = reg m r) ∧
      (∀ q, q ≠ sp → q ≠ a4 → reg n q = reg m q) := by
  have hc := C.env.cod
  have s0 : St m.mem EV m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc ev_at_0 (off' := 4) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.self.aluImm hc ev_at_4 (off' := 8) (by decide)
  have sp1 : reg m1 sp = F + BitVec.ofNat 32 0xEB0 := by
    rw [u1.upd_eq (by decide), hsp]; exact add_spm F (by decide)
  have a42 : reg m2 a4 = F + BitVec.ofNat 32 0x1630 := by rw [u2.upd_eq (by decide), sp1]; exact add_sp F rfl
  have r2 : ∀ q, q ≠ sp → q ≠ a4 → reg m2 q = reg m q := fun q h1 h2 => by
    rw [u2.upd_ne u1.self.zero q h2, u1.upd_ne s0.zero q h1]
  have sp2 : reg m2 sp = F + BitVec.ofNat 32 0xEB0 := by rw [u2.upd_ne u1.self.zero sp (by decide), sp1]
  obtain ⟨m3, c3, u3⟩ := St.block (saveBlockR a4 evPs) u2.self hc evSave_end (saveBlockR_ok a4 _ evPs _ fun p hp => by
    have hr := evPs_mem (r := p.1) (o := p.2) hp
    rw [a42, evSl F p.2 (by omega)]
    exact ⟨C.al (by omega), C.codeF (by omega) (by decide) (by rw [ev_len]; decide)⟩)
  rw [saveBlockR_run, a42] at u3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (F + BitVec.ofNat 32 0x1630) (reg m2) evPs = Ms := ⟨_, rfl⟩
  rw [hMs] at u3
  dsimp only at u3
  have hc3 : CodeIn Ms EV ed25519VerifyCode := hc.hi (fun x hx => by
    rw [← hMs]; exact saveMem_outside evPs fun p hp => by
      have hr := evPs_mem (r := p.1) (o := p.2) hp
      rw [evSl F p.2 (by omega)]; exact C.codeF (by omega) hx (by have := x.isLt; omega)) (by decide)
    (by rw [ev_len]; decide)
  obtain ⟨m4, d4, u4⟩ := u3.aluImm hc3 ev_at_38 (off' := 0x3C) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.self.aluImm hc3 ev_at_3c (off' := 0x40) (by decide)
  have sp5 : reg m5 sp = F := by
    rw [u5.upd_eq (by decide), u4.upd_eq (by decide), sp2,
      show aluEval .add (F + BitVec.ofNat 32 0xEB0) 0xFFFFF800 = F + BitVec.ofNat 32 0x6B0 from add_spm F (by decide),
      show aluEval .add (F + BitVec.ofNat 32 0x6B0) 0xFFFFF950 = F + BitVec.ofNat 32 0 from add_spm F (by decide),
      add_ofNat_zero]
  have r5 : ∀ q, q ≠ sp → reg m5 q = reg m2 q := fun q h => by
    rw [u5.upd_ne u4.self.zero q h, u4.upd_ne u3.zero q h]
  refine ⟨m5, Ms, .cons d1 (.cons d2 (c3.trans (.cons d4 (.single d5)))),
    ⟨u5.self, sp5, by rw [r5 _ (by decide), r2 _ (by decide) (by decide)],
      by rw [r5 _ (by decide), r2 _ (by decide) (by decide)], fun x hx => ?_, fun _ _ _ => rfl⟩,
    fun r o hm => ?_, fun q h1 h2 => by rw [r5 q h1, r2 q h1 h2]⟩
  · rw [← hMs]; exact saveMem_outside evPs fun p hp => by
      have hr := evPs_mem (r := p.1) (o := p.2) hp
      rw [evSl F p.2 (by omega)]; exact C.inG (by omega) hx
  · have hr := evPs_mem hm
    rw [← hMs, saveMem_slot evPs _ hm (evPs_slot hm), r2 r hr.1 hr.2.1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From offset 0x100A: the epilogue, returning `a0`, with the slots
holding `rM`'s saved registers. -/
theorem ev_fin {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}
    {M : Word → BitVec 8} {n : Machine} (C : EvCtx M0 F pk sig msg len) (D : EvSt M0 Ms F r0 M n 0x100A)
    {rM : Fin 32 → Word} (hsl : ∀ r o, (r, o) ∈ evPs → memLoad32 Ms (F + BitVec.ofNat 32 0x1630 + o) = rM r)
    (hret : rM ra &&& ~~~1 = rM ra) :
    ∃ m', Steps n m' ∧ m'.pc = rM ra ∧ reg m' sp = F + BitVec.ofNat 32 0x16A0 ∧ reg m' a0 = reg n a0 ∧
      (∀ r o, (r, o) ∈ evPs → reg m' r = rM r) ∧ reg m' 3 = r0 3 ∧ reg m' 4 = r0 4 ∧ m'.mem = M := by
  have hc := D.code C
  have s := D.st
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc ev_at_100a (off' := 0x100E) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc ev_at_100e (off' := 0x1012) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc ev_at_1012 (off' := 0x1016) (by decide)
  have sp2 : reg n2 sp = F + BitVec.ofNat 32 0xEB0 := by
    rw [u2.upd_eq (by decide), u1.upd_eq (by decide), D.hsp,
      show aluEval .add F 0x7F0 = F + BitVec.ofNat 32 0x7F0 from rfl,
      show aluEval .add (F + BitVec.ofNat 32 0x7F0) 0x6C0 = F + BitVec.ofNat 32 0xEB0 from add_sp F rfl]
  have a13 : reg n3 a1 = F + BitVec.ofNat 32 0x1630 := by rw [u3.upd_eq (by decide), sp2]; exact add_sp F rfl
  have r3 : ∀ q, q ≠ sp → q ≠ a1 → reg n3 q = reg n q := fun q h1 h2 => by
    rw [u3.upd_ne u2.self.zero q h2, u2.upd_ne u1.self.zero q h1, u1.upd_ne s.zero q h1]
  have sp3 : reg n3 sp = F + BitVec.ofNat 32 0xEB0 := by rw [u3.upd_ne u2.self.zero _ (by decide), sp2]
  have hal : ∀ p ∈ evPs, (F + BitVec.ofNat 32 0x1630 + p.2).toNat % 4 = 0 := fun p hp => by
    have hr := evPs_mem (r := p.1) (o := p.2) hp
    rw [evSl F p.2 (by omega)]; exact C.al (by omega)
  obtain ⟨n4, c4, u4⟩ := St.block (restoreBlockR a1 evPs) u3.self hc evRestore_end
    (restoreBlockR_ok _ (F + BitVec.ofNat 32 0x1630) a1 (by decide) evPs _ a13 evPs_a1 hal)
  rw [restoreBlockR_run _ (F + BitVec.ofNat 32 0x1630) a1 (by decide) evPs _ a13 evPs_a1] at u4
  dsimp only at u4
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc ev_at_1046 (off' := 0x104A) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr hc ev_at_104a
  have slotM : ∀ r o, (r, o) ∈ evPs → memLoad32 M (F + BitVec.ofNat 32 0x1630 + o) = rM r := fun r o hm => by
    have hr := evPs_mem hm
    rw [← hsl r o hm, evSl F o (by omega)]; exact D.slotW (by omega) (by omega)
  have oth : ∀ q : Fin 32, q ≠ sp → (∀ p ∈ evPs, p.1 ≠ q) → q.val ≠ 0 →
      reg n6 q = upd (reg n) a1 (F + BitVec.ofNat 32 0x1630) q := fun q hq hps h0 => by
    rw [regs6, u5.regs, upd_ne h0 hq, restoreRegs_other _ _ evPs _ q h0 hps]
    by_cases e : q = a1
    · rw [e, a13]; simp +decide only [upd_app, ↓reduceIte]
    · rw [r3 q hq e, upd_ne h0 e]
  have spR : restoreRegs M (F + BitVec.ofNat 32 0x1630) (reg n3) evPs sp = F + BitVec.ofNat 32 0xEB0 := by
    rw [restoreRegs_other _ _ evPs _ sp (by decide) (by decide), sp3]
  refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.single d6))))), ?_, ?_, ?_, fun r o hm => ?_,
    ?_, ?_, by rw [mem6]⟩
  · rw [pc6, u5.regs, upd_ne (by decide) (by decide), evPs_restore _ _ _ ra (BitVec.ofNat 32 0x6C) (by decide),
      slotM ra _ (by decide), add_lit_zero, hret]
  · rw [regs6, u5.regs]; simp only [upd_app, ↓reduceIte]; rw [spR]; exact add_sp F rfl
  · rw [oth a0 (by decide) (by decide) (by decide), upd_ne (by decide) (by decide)]
  · have hr := evPs_mem hm
    rw [regs6, u5.regs, upd_ne hr.2.2.2.1 hr.1, evPs_restore _ _ _ r o hm, slotM r o hm]
  · rw [oth 3 (by decide) (by decide) (by decide), upd_ne (by decide) (by decide), D.gp]
  · rw [oth 4 (by decide) (by decide) (by decide), upd_ne (by decide) (by decide), D.tp]

end C3.RV32
