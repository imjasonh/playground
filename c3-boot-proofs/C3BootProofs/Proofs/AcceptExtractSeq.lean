import C3BootProofs.Proofs.AcceptExtract

/-!
# The extract stage from its sub-stages

`ac_extract` composes the six sub-stages of `AcceptExtract` into
`AcExtractStage`. `ace_extract_spec` turns the keys the loops read into
`extractTrustedRoot`'s result, `ace_keys_snoc` is one loop step of the
spec, and `AceKeysIn.sv` and `AceKeysIn.transfer` hand the arrays to
`SvRootAt` after later stages copy them.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

/-! ## Sequencing -/

/-- A stage that ends where the next one starts. -/
theorem AcStage.seq {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n0 : Machine} {o1 o2 : Nat}
    {Q1 Q2 : Machine → Prop} (h1 : AcStage B Bf g t r v M0 n0 o1 Q1)
    (h2 : ∀ n1, AcInv B Bf g t v M0 n1 → n1.pc = AC + BitVec.ofNat 32 o1 → Q1 n1 →
      AcStage B Bf g t r v M0 n1 o2 Q2) :
    AcStage B Bf g t r v M0 n0 o2 Q2 := by
  obtain ⟨n1, s1, h⟩ := h1
  rcases h with h | ⟨I1, h | ⟨hp, hq⟩⟩
  · exact ⟨n1, s1, .inl h⟩
  · exact ⟨n1, s1, .inr ⟨I1, .inl h⟩⟩
  · obtain ⟨n2, s2, h2'⟩ := h2 n1 I1 hp hq
    exact ⟨n2, s1.trans s2, h2'⟩

/-- **The extract stage**, from its six sub-stages. -/
theorem ac_extract (hH : AceHeadStage) (hC : AceCaStage) (hT : AceTlogStage) (hS : AceTsaStage)
    (hD : AceDupStage) (hE : AceTailStage) : AcExtractStage := by
  intro n B Bf g t r D v M0 json env lay code st inv pre
  let X : AceCtx := ⟨B, Bf, g, t, r, D, v, M0, n, json⟩
  have ok : X.Ok := ⟨env, lay, code, st, inv, pre⟩
  refine AcStage.seq (hH X ok) fun n1 _ _ h1 => ?_
  obtain ⟨fp1, jr, cas, A1, C1⟩ := h1
  refine AcStage.seq (hC X ok n1 fp1 jr cas [] A1 C1) fun n2 _ _ h2 => ?_
  obtain ⟨fp2, fs, tlogs, A2, T2⟩ := h2
  refine AcStage.seq (hT X ok n2 fp2 jr fs tlogs [] A2 T2) fun n3 _ _ h3 => ?_
  obtain ⟨fp3, ls, tsas, A3, S3⟩ := h3
  refine AcStage.seq (hS X ok n3 fp3 jr fs ls tsas [] A3 S3) fun n4 _ _ h4 => ?_
  obtain ⟨fp4, ts, A4, K4⟩ := h4
  refine AcStage.seq (hD X ok n4 fp4 fs ls ts A4 K4) fun n5 _ _ h5 => ?_
  obtain ⟨A5, K5, D5⟩ := h5
  exact hE X ok n5 fp4 fs ls ts A5 K5 D5

/-! ## The spec -/

/-- One more item for `aceKeys`. -/
theorem ace_keys_snoc {α : Type} {f : Json → Option (Option α)} {done : List Json} {ks : List α} {j : Json}
    {k : Option α} (h : aceKeys f done = some ks) (hj : f j = some k) :
    aceKeys f (done ++ [j]) = some (ks ++ k.toList) := by
  unfold aceKeys at h ⊢
  obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [List.mapM_append, hz, List.mapM_cons, hj, List.mapM_nil]
  cases k <;> simp

/-- One more item for `AceProg`. -/
theorem AceProg.step {α : Type} {jr : Json} {key : Bytes} {f : Json → Option (Option α)} {j : Json}
    {rest : List Json} {ks : List α} {k : Option α} (h : AceProg jr key f (j :: rest) ks) (hj : f j = some k) :
    AceProg jr key f rest (ks ++ k.toList) := by
  obtain ⟨done, ha, hk⟩ := h
  exact ⟨done ++ [j], by rw [List.append_assoc]; exact ha, ace_keys_snoc hk hj⟩

/-- **The keys the loops read are `extractTrustedRoot`'s.** -/
theorem ace_extract_spec {json : Bytes} {jr : Json} {fs : List FulcioKey} {ls : List LogKey} {ts : List TsaKey}
    (hr : AceRootJ json jr) (hc : AceProg jr (ascii!"certificateAuthorities") aceCa [] fs)
    (hl : AceProg jr (ascii!"tlogs") logEntry [] ls) (ht : AceProg jr (ascii!"timestampAuthorities") aceTsa [] ts)
    (hfl : fs.length ≤ 8) (hll : ls.length ≤ 16) (htl : ts.length ≤ 8) (hd : AceDistinct fs ls ts)
    (pol : Policy) : extractTrustedRoot json pol = some ⟨fs, ls, ts, pol⟩ := by
  obtain ⟨hp, hm⟩ := hr
  obtain ⟨cas, hca, hcs⟩ := hc
  obtain ⟨tlogs, hta, hts⟩ := hl
  obtain ⟨tsas, hsa, hss⟩ := ht
  rw [List.append_nil] at hca hta hsa
  unfold aceKeys at hcs hts hss
  obtain ⟨cs, hcz, rfl⟩ := Option.map_eq_some_iff.mp hcs
  obtain ⟨lz, hlz, rfl⟩ := Option.map_eq_some_iff.mp hts
  obtain ⟨sz, hsz, rfl⟩ := Option.map_eq_some_iff.mp hss
  unfold AceDistinct at hd
  unfold extractTrustedRoot
  delta aceCa aceTsa at hcz hsz
  simp only [Option.bind_eq_bind, Option.pure_def, aceMediaType] at hm hca hta hsa hcz hsz
  have hb : ((Json.field (ascii!"mediaType") jr).bind asStr ==
      some (ascii!"application/vnd.dev.sigstore.trustedroot+json;version=0.1")) = true := by
    rw [hm]; rfl
  simp only [hp, hb, hca, hta, hsa, Option.bind_eq_bind, Option.bind_some, require,
    ↓reduceIte, Option.pure_def, hcz, hlz]
  erw [hsz]
  have h1 : (decide ((cs.filterMap id).length ≤ 8) && decide ((lz.filterMap id).length ≤ 16) &&
      decide ((sz.filterMap id).length ≤ 8)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hfl, hll⟩, htl⟩
  simp only [h1, hd, ↓reduceIte, Option.bind_some]

/-! ## The arrays in `SvRootAt` -/

theorem SvArrayAt.mono {α : Type} {M : Word → BitVec 8} {a : Word} {cap : Nat} {l : List α}
    {f g : Word → α → Prop} (h : SvArrayAt M a cap l f) (hfg : ∀ e x, f e x → g e x) : SvArrayAt M a cap l g :=
  ⟨h.1, fun i hi => hfg _ _ (h.2.1 i hi), h.2.2⟩

/-- Bytes in `Buffers` from `doc` on lie outside `sigstoreVerify`'s stack
when `Buffers` does. -/
theorem ace_svIn {Bs Bf p : Word} {l : Nat} (hs : SvIn Bs Bf acBufLen) (hlo : Bf.toNat + 0x4000 ≤ p.toNat)
    (hhi : p.toNat + l ≤ Bf.toNat + 0xB840) : SvIn Bs p l := by
  have hw := hs.lo
  unfold acBufLen at hw
  have e : p = Bf + BitVec.ofNat 32 (p.toNat - Bf.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  exact (hs.sub (c := p.toNat - Bf.toNat) (l := l) (by unfold acBufLen; omega)).ptr e

theorem AceEntryIn.sv {Bs Bf fp : Word} {M : Word → BitVec 8} {e : Word} {name key : Bytes} {n : Nat} {w : Window}
    (hs : SvIn Bs Bf acBufLen) (hfp : fp.toNat ≤ Bf.toNat + 0xB840) (h : AceEntryIn Bf fp M e name key n w) :
    SvEntryAt Bs M e name key n w where
  ne := fun h0 => by have := h.name.1; rw [h0] at this; simp at this
  name := ⟨ace_svIn hs h.name.1 (by have := h.name.2.1; omega), h.name.2.2⟩
  notBefore := h.notBefore
  notAfter := h.notAfter
  keyIn := ace_svIn hs h.key.1 (by have := h.key.2.1; omega)
  key := h.key.2.2

/-- **The arrays at `r + 0x28` are `SvRootAt`'s.** -/
theorem AceKeysIn.sv {Bs Bf fp : Word} {M : Word → BitVec 8} {r : Word} {fs : List FulcioKey} {ls : List LogKey}
    {ts : List TsaKey} (hs : SvIn Bs Bf acBufLen) (hfp : fp.toNat ≤ Bf.toNat + 0xB840)
    (h : AceKeysIn Bf fp M (r + 0x28) fs ls ts) :
    SvArrayAt M (r + 0x28) 8 fs (fun e k => SvEntryAt Bs M e k.subject k.publicKey 0x61 k.window) ∧
    SvArrayAt M (r + 0x128) 16 ls (fun e k => SvEntryAt Bs M e k.origin k.publicKey 32 k.window) ∧
    SvArrayAt M (r + 0x328) 8 ts (fun e k => SvEntryAt Bs M e k.signerId k.publicKey 0x61 k.window) := by
  obtain ⟨hf, hl, ht⟩ := h
  have e1 : r + 0x28 + 0x100 = r + 0x128 := by rw [BitVec.add_assoc]; rfl
  have e2 : r + 0x28 + 0x300 = r + 0x328 := by rw [BitVec.add_assoc]; rfl
  rw [AceLogsAt, e1] at hl
  rw [AceTsasAt, e2] at ht
  exact ⟨SvArrayAt.mono hf fun _ _ x => x.sv hs hfp, SvArrayAt.mono hl fun _ _ x => x.sv hs hfp,
    SvArrayAt.mono ht fun _ _ x => x.sv hs hfp⟩

end C3.RV32.Ac
