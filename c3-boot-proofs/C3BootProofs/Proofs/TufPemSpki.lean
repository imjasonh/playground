import C3BootProofs.Proofs.TufCalls
import C3BootProofs.Proofs.StripPrefix
import C3BootProofs.Proofs.Base64Decode
import C3BootProofs.Proofs.MemsetAny
import C3BootProofs.Image.BootloaderData8
import C3BootProofs.Spec.Tuf

/-!
# `tuf::pem_spki`, as compiled

`pem_spki(pem, out)` strips the PEM header with `strip_prefix` and checks
the footer with `equal_same_length`, copies the bytes between them other
than line feeds into a 192-byte buffer on the stack, and decodes that text
into the 128 bytes at `out` with `base64::decode_into`. It returns the
decoded slice's address in `a0` and its length in `a1`, or a null pointer.

The function keeps five registers in a 0xE0-byte frame, and
`decode_into` uses 0x50 more bytes, so the stack region is the 304 bytes
below `sp`. `tufPemSpki_correct` is the contract, against `pemSpkiModel`.
-/

namespace C3.Json

/-- The bytes of a PEM text other than line feeds. -/
def pemNoLf (l : Bytes) : Bytes := l.filter (· != 0x0A)

/-- The key that `pem_spki` decodes from the text between the lines: the
text's base64, when the text has at most 192 bytes and the key at most 128. -/
def pemDecode (text : Bytes) : Option Bytes :=
  if text.length ≤ 192 then
    match base64Decode text with
    | some bs => if bs.length ≤ 128 then some bs else none
    | none => none
  else none

/-- `tuf::pem_spki`: the base64 text between the header and footer lines,
without line feeds, decoded by `pemDecode`. -/
def pemSpkiModel (pem : Bytes) : Option Bytes :=
  if pem.take 27 = ascii!"-----BEGIN PUBLIC KEY-----\n" ∧ 52 ≤ pem.length ∧
      pem.drop (pem.length - 25) = ascii!"-----END PUBLIC KEY-----\n" then
    pemDecode (pemNoLf ((pem.drop 27).take (pem.length - 52)))
  else none

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

abbrev TPS : Word := BitVec.ofNat 32 tufPemSpkiAddress
abbrev TPS_SP : Word := BitVec.ofNat 32 stripPrefixAddress
abbrev TPS_ESL : Word := BitVec.ofNat 32 equalSameLengthAddress
abbrev TPS_MC : Word := BitVec.ofNat 32 memcmpAddress
abbrev TPS_MS : Word := BitVec.ofNat 32 memsetAddress
abbrev TPS_HDR : Word := BitVec.ofNat 32 tufPemHeaderAddress
abbrev TPS_FTR : Word := BitVec.ofNat 32 tufPemFooterAddress

theorem tps_at_0 : fetchRel tufPemSpkiCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF20, 2) := by decide
theorem tps_at_2 : fetchRel tufPemSpkiCode 0x2 = some (.store .sw sp ra 0xDC, 2) := by decide
theorem tps_at_4 : fetchRel tufPemSpkiCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xD8, 2) := by decide
theorem tps_at_6 : fetchRel tufPemSpkiCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xD4, 2) := by decide
theorem tps_at_8 : fetchRel tufPemSpkiCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xD0, 2) := by decide
theorem tps_at_a : fetchRel tufPemSpkiCode 0xA = some (.store .sw sp (19 : Fin 32) 0xCC, 2) := by decide
theorem tps_at_c : fetchRel tufPemSpkiCode 0xC = some (.alu .add (18 : Fin 32) x0 a2, 2) := by decide
theorem tps_at_e : fetchRel tufPemSpkiCode 0xE = some (.lui a2 0x3FCC5000, 4) := by decide
theorem tps_at_12 : fetchRel tufPemSpkiCode 0x12 = some (.aluImm .add a2 a2 0xFFFFF8BE, 4) := by decide
theorem tps_at_16 : fetchRel tufPemSpkiCode 0x16 = some (.aluImm .add a3 x0 0x1B, 2) := by decide
theorem tps_at_18 : fetchRel tufPemSpkiCode 0x18 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem tps_at_1c : fetchRel tufPemSpkiCode 0x1C = some (.jalr ra ra 0xAA, 4) := by decide
theorem tps_at_20 : fetchRel tufPemSpkiCode 0x20 = some (.branch .beq a0 x0 0x68, 2) := by decide
theorem tps_at_22 : fetchRel tufPemSpkiCode 0x22 = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem tps_at_24 : fetchRel tufPemSpkiCode 0x24 = some (.aluImm .add a0 x0 0x19, 2) := by decide
theorem tps_at_26 : fetchRel tufPemSpkiCode 0x26 = some (.branch .bgeu a1 a0 0x8, 4) := by decide
theorem tps_at_2a : fetchRel tufPemSpkiCode 0x2A = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem tps_at_2c : fetchRel tufPemSpkiCode 0x2C = some (.jal x0 0x5C, 2) := by decide
theorem tps_at_2e : fetchRel tufPemSpkiCode 0x2E = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem tps_at_30 : fetchRel tufPemSpkiCode 0x30 = some (.aluImm .add (8 : Fin 32) a1 0xFFFFFFE7, 4) := by decide
theorem tps_at_34 : fetchRel tufPemSpkiCode 0x34 = some (.lui a1 0x3FCC5000, 4) := by decide
theorem tps_at_38 : fetchRel tufPemSpkiCode 0x38 = some (.aluImm .add a1 a1 0xFFFFF8D9, 4) := by decide
theorem tps_at_3c : fetchRel tufPemSpkiCode 0x3C = some (.aluImm .add a2 x0 0x19, 2) := by decide
theorem tps_at_3e : fetchRel tufPemSpkiCode 0x3E = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem tps_at_40 : fetchRel tufPemSpkiCode 0x40 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem tps_at_44 : fetchRel tufPemSpkiCode 0x44 = some (.jalr ra ra 0x6C, 4) := by decide
theorem tps_at_48 : fetchRel tufPemSpkiCode 0x48 = some (.branch .beq a0 x0 0x40, 2) := by decide
theorem tps_at_4a : fetchRel tufPemSpkiCode 0x4A = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem tps_at_4c : fetchRel tufPemSpkiCode 0x4C = some (.aluImm .add a2 x0 0xC0, 4) := by decide
theorem tps_at_50 : fetchRel tufPemSpkiCode 0x50 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem tps_at_52 : fetchRel tufPemSpkiCode 0x52 = some (.aluImm .add (19 : Fin 32) sp 0x4, 4) := by decide
theorem tps_at_56 : fetchRel tufPemSpkiCode 0x56 = some (.auipc ra 0xB000, 4) := by decide
theorem tps_at_5a : fetchRel tufPemSpkiCode 0x5A = some (.jalr ra ra 0x434, 4) := by decide
theorem tps_at_5e : fetchRel tufPemSpkiCode 0x5E = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem tps_at_60 : fetchRel tufPemSpkiCode 0x60 = some (.aluImm .add a0 x0 0xA, 2) := by decide
theorem tps_at_62 : fetchRel tufPemSpkiCode 0x62 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem tps_at_64 : fetchRel tufPemSpkiCode 0x64 = some (.branch .beq a3 (8 : Fin 32) 0x32, 4) := by decide
theorem tps_at_68 : fetchRel tufPemSpkiCode 0x68 = some (.load .lbu a1 a3 0x0, 4) := by decide
theorem tps_at_6c : fetchRel tufPemSpkiCode 0x6C = some (.aluImm .add (9 : Fin 32) a3 0x1, 4) := by decide
theorem tps_at_70 : fetchRel tufPemSpkiCode 0x70 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem tps_at_72 : fetchRel tufPemSpkiCode 0x72 = some (.branch .beq a1 a0 0xFFFFFFF2, 4) := by decide
theorem tps_at_76 : fetchRel tufPemSpkiCode 0x76 = some (.aluImm .add a3 a2 0xFFFFFF40, 4) := by decide
theorem tps_at_7a : fetchRel tufPemSpkiCode 0x7A = some (.branch .beq a3 x0 0xFFFFFFB0, 2) := by decide
theorem tps_at_7c : fetchRel tufPemSpkiCode 0x7C = some (.alu .add a3 (19 : Fin 32) a2, 4) := by decide
theorem tps_at_80 : fetchRel tufPemSpkiCode 0x80 = some (.aluImm .add a2 a2 0x1, 2) := by decide
theorem tps_at_82 : fetchRel tufPemSpkiCode 0x82 = some (.store .sb a3 a1 0x0, 4) := by decide
theorem tps_at_86 : fetchRel tufPemSpkiCode 0x86 = some (.jal x0 0xFFFFFFDC, 2) := by decide
theorem tps_at_88 : fetchRel tufPemSpkiCode 0x88 = some (.load .lw ra sp 0xDC, 2) := by decide
theorem tps_at_8a : fetchRel tufPemSpkiCode 0x8A = some (.load .lw (8 : Fin 32) sp 0xD8, 2) := by decide
theorem tps_at_8c : fetchRel tufPemSpkiCode 0x8C = some (.load .lw (9 : Fin 32) sp 0xD4, 2) := by decide
theorem tps_at_8e : fetchRel tufPemSpkiCode 0x8E = some (.load .lw (18 : Fin 32) sp 0xD0, 2) := by decide
theorem tps_at_90 : fetchRel tufPemSpkiCode 0x90 = some (.load .lw (19 : Fin 32) sp 0xCC, 2) := by decide
theorem tps_at_92 : fetchRel tufPemSpkiCode 0x92 = some (.aluImm .add sp sp 0xE0, 2) := by decide
theorem tps_at_94 : fetchRel tufPemSpkiCode 0x94 = some (.jalr x0 ra 0x0, 2) := by decide
theorem tps_at_96 : fetchRel tufPemSpkiCode 0x96 = some (.aluImm .add a0 x0 0xC1, 4) := by decide
theorem tps_at_9a : fetchRel tufPemSpkiCode 0x9A = some (.branch .bgeu a2 a0 0xFFFFFF90, 4) := by decide
theorem tps_at_9e : fetchRel tufPemSpkiCode 0x9E = some (.aluImm .add a0 sp 0xC4, 2) := by decide
theorem tps_at_a0 : fetchRel tufPemSpkiCode 0xA0 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem tps_at_a2 : fetchRel tufPemSpkiCode 0xA2 = some (.aluImm .add a4 x0 0x80, 4) := by decide
theorem tps_at_a6 : fetchRel tufPemSpkiCode 0xA6 = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem tps_at_a8 : fetchRel tufPemSpkiCode 0xA8 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem tps_at_ac : fetchRel tufPemSpkiCode 0xAC = some (.jalr ra ra 0x708, 4) := by decide
theorem tps_at_b0 : fetchRel tufPemSpkiCode 0xB0 = some (.load .lbu a0 sp 0xC4, 4) := by decide
theorem tps_at_b4 : fetchRel tufPemSpkiCode 0xB4 = some (.branch .bne a0 x0 0xFFFFFF76, 2) := by decide
theorem tps_at_b6 : fetchRel tufPemSpkiCode 0xB6 = some (.load .lw a1 sp 0xC8, 2) := by decide
theorem tps_at_b8 : fetchRel tufPemSpkiCode 0xB8 = some (.aluImm .sltu a0 a1 0x81, 4) := by decide
theorem tps_at_bc : fetchRel tufPemSpkiCode 0xBC = some (.alu .sub a0 x0 a0, 4) := by decide
theorem tps_at_c0 : fetchRel tufPemSpkiCode 0xC0 = some (.alu .and a0 a0 (18 : Fin 32), 4) := by decide
theorem tps_at_c4 : fetchRel tufPemSpkiCode 0xC4 = some (.jal x0 0xFFFFFFC4, 2) := by decide

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `strip_prefix(s, pre)` with the code at `tb`, whose frame is
the 20 bytes at `r`. -/
theorem WP.callStrip {hi lo tb s pre r : Word} {sl pl : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb stripPrefixCode) (hce : CodeIn M (tb + 0xFFFFFFEA) equalSameLengthCode)
    (hcm : CodeIn M (tb + 0xFFFFFFEA + 0xD3BE) memcmpCode)
    (h0 : f a0 = s) (ha1 : f a1 = BitVec.ofNat 32 sl) (ha2 : f a2 = pre) (ha3 : f a3 = BitVec.ofNat 32 pl)
    (hsl : sl < 2 ^ 32) (hpl : pl < 2 ^ 32) (hsp : f sp + 0xFFFFFFEC = r) (hal : (f sp).toNat % 4 = 0)
    (sSC : Sep r 20 tb stripPrefixCode.length) (sSE : Sep r 20 (tb + 0xFFFFFFEA) equalSameLengthCode.length)
    (sSM : Sep r 20 (tb + 0xFFFFFFEA + 0xD3BE) memcmpCode.length) (sSS : Sep r 20 s sl) (sSP : Sep r 20 pre pl)
    (hsc : Sep r 20 base code.length)
    (k : ∀ m2 : Machine,
      reg m2 a0 = (if pl ≤ sl ∧ memBytes M s pl = memBytes M pre pl then s + BitVec.ofNat 32 pl else 0) →
      (pl ≤ sl → reg m2 a1 = BitVec.ofNat 32 (sl - pl)) → Out M m2.mem r 20 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 eslClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := eslClob)
    (P := fun m2 => reg m2 a0 = (if pl ≤ sl ∧ memBytes M s pl = memBytes M pre pl then s + BitVec.ofNat 32 pl
      else 0) ∧ (pl ≤ sl → reg m2 a1 = BitVec.ofNat 32 (sl - pl)) ∧ Out M m2.mem r 20)
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.2.codeIn hc hsc) (fun m2 hP => k m2 hP.1 hP.2.1 hP.2.2)
  have hs1 : reg m1 sp = f sp := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, r0, r1, hfr, hmf⟩ := stripPrefix_correct m1 (base := tb) (s := s) (pre := pre) (sl := sl)
    (pl := pl) (by rw [hmem1]; exact hct) htb (by rw [hmem1]; exact hce) (by rw [hmem1]; exact hcm) hpc1
    (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (by rw [hreg1]; rsimp; exact ha3) hsl hpl
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    (by rw [hs1]; exact hal) (by rw [hs1, hsp]; exact sSC) (by rw [hs1, hsp]; exact sSE)
    (by rw [hs1, hsp]; exact sSM) (by rw [hs1, hsp]; exact sSS) (by rw [hs1, hsp]; exact sSP)
  rw [hmem1] at r0
  refine ⟨m2, c2, pc2, ⟨r0, r1, fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [hmf x (by rw [hs1, hsp]; exact hx.symm), hmem1]
  · simp only [eslClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨n0, n1, n2, n3, n4⟩ := hx
    exact hfr x n0 n1 n2 n3 n4

/-- The registers `memset` may change. -/
abbrev tpsMsClob : List (Fin 32) := [a2, a3, a4, a5, a6]

/-- A call to `memset(dst, b, n)` with the code at `tb`. -/
theorem WP.callMemsetT {hi lo tb dst b : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb memsetCode) (h0 : f a0 = dst) (ha1 : f a1 = b) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hwrap : dst.toNat + n < 2 ^ 32) (hDC : Sep dst n tb memsetCode.length) (hDB : Sep dst n base code.length)
    (k : ∀ m2 : Machine, m2.mem = fillBytes M dst (b.extractLsb' 0 8) n →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 tpsMsClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := tpsMsClob) (P := fun m2 => m2.mem = fillBytes M dst (b.extractLsb' 0 8) n)
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by rw [hP]; exact hc.fillBytes hDB (Nat.le_refl _)) k
  obtain ⟨m2, c2, pc2, mem2, -, hfr⟩ := memset_correct m1 tb (base + BitVec.ofNat 32 (off + 8)) dst b n
    (fun i hi => by rw [hmem1]; exact hct i hi) htb hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev)) hwrap hDC
  rw [hmem1] at mem2
  refine ⟨m2, c2, pc2, mem2, fun x hx => ?_⟩
  simp only [tpsMsClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨n2, n3, n4, n5, n6⟩ := hx
  exact hfr x n2 n3 n4 n5 n6

/-- What `base64::decode_into` leaves for the `n` bytes at `t`, with its
stack the 0x50 bytes below `sp0`. -/
def TpsB64Res (M M' : Word → BitVec 8) (sp0 res t out : Word) (n L : Nat) : Prop :=
  (∀ bs, base64Decode (memBytes M t n) = some bs → bs.length ≤ L →
    M' res = 0 ∧ memLoad32 M' (res + 4) = BitVec.ofNat 32 bs.length ∧ memBytes M' out bs.length = bs) ∧
  ((∀ bs, base64Decode (memBytes M t n) = some bs → L < bs.length) → M' res = 1) ∧
  ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → Sep out L x 1 → Sep res 8 x 1 → M' x = M x

/-- A call to `base64::decode_into` on the `n` bytes at `t`, into the `L`
bytes at `out`, with the result at `res`. -/
theorem WP.callB64 {hi lo sp0 res t out : Word} {n L : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BDI) (hev : (off + 8) % 2 = 0)
    (hc : CodeIn M BDI base64DecodeIntoCode) (hcW : CodeIn M BCW copyFromSliceU8Code)
    (hcS : CodeIn M BMS memcpyStubCode) (hcB : CodeIn M BMB memcpyBodyCode)
    (h0 : f a0 = res) (ha1 : f a1 = t) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = out)
    (ha4 : f a4 = BitVec.ofNat 32 L) (hsp : f sp = sp0) (hsa : sp0.toNat % 4 = 0) (hsl : 0x50 ≤ sp0.toNat)
    (hsw : sp0.toNat ≤ 0x40000000) (hres : res.toNat + 8 ≤ 0x40000000) (hra4 : res.toNat % 4 = 0)
    (hdw : out.toNat + L ≤ 0x40000000) (htw : t.toNat + n ≤ 0x40000000)
    (sOG : Sep out L (sp0 + 0xFFFFFFB0) 0x50) (sTG : Sep t n (sp0 + 0xFFFFFFB0) 0x50)
    (sRG : Sep res 8 (sp0 + 0xFFFFFFB0) 0x50) (sTO : Sep t n out L) (sRO : Sep res 8 out L)
    (hSb : Sep (sp0 + 0xFFFFFFB0) 0x50 base code.length) (hob : Sep out L base code.length)
    (hrb : Sep res 8 base code.length)
    (k : ∀ m2 : Machine, TpsB64Res M m2.mem sp0 res t out n L →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := BDI) (cl := jClob) (P := fun m2 => TpsB64Res M m2.mem sp0 res t out n L)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc i hi => by
      rw [hP.2.2 _ (hSb.symm.sub (c := i) (l := 1) hi).symm (hob.symm.sub (c := i) (l := 1) hi).symm
        (hrb.symm.sub (c := i) (l := 1) hi).symm]
      exact hc i hi) k
  obtain ⟨m2, c2, pc2, rsp, hkeep, hok, herr, hfr⟩ := base64DecodeInto_correct m1 (sp0 := sp0) (res := res)
    (t := t) (out := out) (n := n) (L := L) (by rw [hmem1]; exact hc) (by rw [hmem1]; exact hcW)
    (by rw [hmem1]; exact hcS) (by rw [hmem1]; exact hcB) hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact ha3)
    (by rw [hreg1]; rsimp; exact ha4) (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev)) (by rw [hreg1]; rsimp; exact hsp) hsa hsl hsw hres hra4 hdw htw
    sOG sTG sRG sTO sRO
  rw [hmem1] at hok herr hfr
  refine ⟨m2, c2, pc2, ⟨hok, herr, fun x h1 h2 h3 => hfr x h1 h2 h3⟩, fun x hx => ?_⟩
  have hsp1 : reg m1 sp = sp0 := by rw [hreg1]; rsimp; exact hsp
  by_cases hx0 : x.val = 0
  · simp only [reg, hx0, ↓reduceIte]
  by_cases hx2 : x = sp
  · rw [hx2, rsp, hsp1]
  refine hkeep x ?_
  revert hx hx0 hx2
  revert x
  decide

end

/-- The filtered prefix grows by the next byte unless it is a line feed. -/
theorem tps_noLf_snoc (l : Bytes) (b : Nat) :
    pemNoLf (l ++ [b]) = pemNoLf l ++ (if b = 0x0A then [] else [b]) := by
  unfold pemNoLf
  rw [List.filter_append]
  by_cases h : b = 0x0A
  · subst h; rfl
  · simp [h]

theorem tps_noLf_len_le (l l' : Bytes) : (pemNoLf l).length ≤ (pemNoLf (l ++ l')).length := by
  unfold pemNoLf; rw [List.filter_append, List.length_append]; omega

theorem tps_ze_beq : ∀ b : BitVec 8, branchTaken .beq (b.zeroExtend 32) (10 : Word) = decide (b.toNat = 10) := by
  decide

theorem tps_beq_cur {q : Word} {i bl : Nat} (hq : q.toNat + bl < 2 ^ 32) (hi : i ≤ bl) :
    branchTaken .beq (q + BitVec.ofNat 32 i) (q + BitVec.ofNat 32 bl) = decide (i = bl) := by
  by_cases h : i = bl
  · subst h; rw [decide_eq_true rfl]; exact beq_iff_eq.mpr rfl
  · rw [decide_eq_false h]
    simp only [branchTaken, beq_eq_false_iff_ne]
    exact add_ofNat_ne q (by omega) (by omega) h

theorem tps_beq_full {j : Nat} (hj : j ≤ 192) :
    branchTaken .beq (aluEval .add (BitVec.ofNat 32 j) 0xFFFFFF40) 0 = decide (j = 192) := by
  by_cases h : j = 192
  · subst h; decide
  · rw [decide_eq_false h]
    simp only [branchTaken, beq_eq_false_iff_ne, ev_add]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (4294967104 : Word).toNat = 4294967104 from rfl,
      show (0 : Word).toNat = 0 from rfl] at this
    omega

theorem tps_updK {L : List (Fin 32)} {g g0 : Fin 32 → Word} {rd : Fin 32} {v : Word} (hrd : rd ∈ L)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ L → g x = g0 x) : ∀ x, x ∉ L → upd g rd v x = g0 x := fun x hx => by
  have hx1 : x ≠ rd := fun h => hx (by subst h; exact hrd)
  by_cases h0 : x.val = 0
  · have : x = 0 := Fin.ext h0
    subst this; simp only [upd, h0, ↓reduceIte]; exact hz0.symm
  · simp only [upd, h0, hx1, ↓reduceIte]; exact hfr x hx

theorem tps_store_bytes {M : Word → BitVec 8} {T : Word} {j : Nat} {v : BitVec 8} (hj : j < 2 ^ 32) :
    memBytes (memStore8 M (T + BitVec.ofNat 32 j) v) T (j + 1) = memBytes M T j ++ [v.toNat] := by
  rw [memBytes_snoc, memStore8_same]
  congr 1
  exact memBytes_congr fun i hi => memStore8_ne (add_ofNat_ne T (by omega) hj (by omega))

/-- The registers the filter loop changes. -/
abbrev tpsL : List (Fin 32) := [a1, a2, a3, 9]

section
variable {Q : Post} {Mm : Word → BitVec 8} {q T : Word} {bl : Nat} {g0 : Fin 32 → Word}

/-- The filter loop at 0x64, after `i` of the `bl` body bytes at `q`, with
`j` bytes kept in the buffer at `T`. -/
theorem tps_loop (hqw : q.toNat + bl < 2 ^ 32) (hTw : T.toNat + 192 < 2 ^ 32) (hqT : Sep q bl T 192)
    (hTc : Sep T 192 TPS tufPemSpkiCode.length) (h8 : g0 8 = q + BitVec.ofNat 32 bl) (h19 : g0 19 = T)
    (ha0 : g0 a0 = 10) (hz0 : g0 0 = 0)
    (Kok : ∀ (g : Fin 32 → Word) (Mk : Word → BitVec 8),
      g a2 = BitVec.ofNat 32 (pemNoLf (memBytes Mm q bl)).length → (pemNoLf (memBytes Mm q bl)).length ≤ 192 →
      memBytes Mk T (pemNoLf (memBytes Mm q bl)).length = pemNoLf (memBytes Mm q bl) → Out Mm Mk T 192 →
      (∀ x, x ∉ tpsL → g x = g0 x) → WP tufPemSpkiCode TPS Q Mk 0x96 g)
    (Kov : ∀ (g : Fin 32 → Word) (Mk : Word → BitVec 8), 192 < (pemNoLf (memBytes Mm q bl)).length →
      Out Mm Mk T 192 → (∀ x, x ∉ tpsL → g x = g0 x) → WP tufPemSpkiCode TPS Q Mk 0x2A g) :
    ∀ (r i j : Nat) (Mk : Word → BitVec 8) (g : Fin 32 → Word), i + r = bl →
      g a3 = q + BitVec.ofNat 32 i → g 9 = q + BitVec.ofNat 32 i → g a2 = BitVec.ofNat 32 j →
      j = (pemNoLf (memBytes Mm q i)).length → j ≤ 192 → memBytes Mk T j = pemNoLf (memBytes Mm q i) →
      Out Mm Mk T 192 → (∀ x, x ∉ tpsL → g x = g0 x) → WP tufPemSpkiCode TPS Q Mk 0x64 g
  | 0, i, j, Mk, g, hr, h3, h9, h2, hj, hj2, hT, hO, hfr => by
    obtain rfl : i = bl := by omega
    have e8 : g 8 = q + BitVec.ofNat 32 i := by rw [hfr 8 (by decide), h8]
    refine WP.branch tps_at_64 (fun _ => ?_) (fun eb => ?_) <;> wn
    · subst hj; exact Kok g Mk h2 hj2 hT hO hfr
    · exfalso; rw [h3, e8, tps_beq_cur hqw (Nat.le_refl _)] at eb; simp at eb
  | r + 1, i, j, Mk, g, hr, h3, h9, h2, hj, hj2, hT, hO, hfr => by
    have e8 : g 8 = q + BitVec.ofNat 32 bl := by rw [hfr 8 (by decide), h8]
    have e19 : g 19 = T := by rw [hfr 19 (by decide), h19]
    have e0 : g a0 = 10 := by rw [hfr a0 (by decide), ha0]
    refine WP.zero fun hz => ?_
    refine WP.branch tps_at_64 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rw [h3, e8, tps_beq_cur hqw (by omega)] at eb; exact absurd (of_decide_eq_true eb) (by omega)
    have hSb : Sep (q + BitVec.ofNat 32 i) 1 T 192 := hqT.sub (c := i) (l := 1) (by omega)
    have hb : Mk (q + BitVec.ofNat 32 i) = Mm (q + BitVec.ofNat 32 i) := hO _ hSb
    refine WP.lbu tps_at_68 ?_; wn
    refine WP.aluImm tps_at_6c ?_; wn
    refine WP.alu tps_at_70 ?_; wn
    rw [h3, add_lit_zero, hb]
    have hq1 : aluEval .add (q + BitVec.ofNat 32 i) 1 = q + BitVec.ofNat 32 (i + 1) := by
      rw [ev_add]; exact add_ofNat_assoc q i 1
    have hsn := memBytes_snoc Mm q i
    refine WP.branch tps_at_72 (fun eb => ?_) (fun eb => ?_) <;> wn
    · -- A line feed: skip it.
      rsimp at eb
      rw [e0, tps_ze_beq] at eb
      have hlf := of_decide_eq_true eb
      refine tps_loop hqw hTw hqT hTc h8 h19 ha0 hz0 Kok Kov r (i + 1) j Mk _ (by omega) ?_ ?_ ?_ ?_ hj2 ?_ hO ?_
      · rsimp; rw [ev0, hq1]
      · rsimp; exact hq1
      · rsimp; exact h2
      · rw [hsn, tps_noLf_snoc, ite_eq_left hlf, List.append_nil]; exact hj
      · rw [hsn, tps_noLf_snoc, ite_eq_left hlf, List.append_nil]; exact hT
      · repeat refine tps_updK (by decide) hz0 ?_
        exact hfr
    · -- Another byte: keep it, unless the buffer is full.
      rsimp at eb
      rw [e0, tps_ze_beq] at eb
      have hlf : ¬ (Mm (q + BitVec.ofNat 32 i)).toNat = 10 := of_decide_eq_false eb
      have hlen : (pemNoLf (memBytes Mm q (i + 1))).length = j + 1 := by
        rw [hsn, tps_noLf_snoc, ite_eq_right hlf, List.length_append, ← hj]; rfl
      refine WP.aluImm tps_at_76 ?_; wn
      refine WP.branch tps_at_7a (fun eb => ?_) (fun eb => ?_) <;> wn
      · -- The buffer is full.
        rsimp at eb
        rw [h2, tps_beq_full hj2] at eb
        have hj192 := of_decide_eq_true eb
        refine Kov _ Mk ?_ hO ?_
        · have := tps_noLf_len_le (memBytes Mm q (i + 1)) (memBytes Mm (q + BitVec.ofNat 32 (i + 1)) r)
          rw [← memBytes_split, show i + 1 + r = bl by omega, hlen] at this
          omega
        · repeat refine tps_updK (by decide) hz0 ?_
          exact hfr
      · rsimp at eb
        rw [h2, tps_beq_full hj2] at eb
        have hj192 : j ≠ 192 := of_decide_eq_false eb
        refine WP.alu tps_at_7c ?_; wn
        refine WP.aluImm tps_at_80 ?_; wn
        refine WP.sb tps_at_82 (by rsimp; rw [e19, h2, ev_add, add_lit_zero]; exact hTc.sub (c := j) (l := 1) (by omega))
          ?_; wn
        refine WP.jal tps_at_86 (by decide) ?_; wn
        refine WP.alu tps_at_62 ?_; wn
        rw [e19, h2, ev_add, add_lit_zero]
        refine tps_loop hqw hTw hqT hTc h8 h19 ha0 hz0 Kok Kov r (i + 1) (j + 1) _ _ (by omega) ?_ ?_ ?_ hlen.symm
          (by omega) ?_ ?_ ?_
        · rsimp; rw [ev0, hq1]
        · rsimp; exact hq1
        · rsimp; rw [ev_add]; exact ofNat_add_lit j 1
        · rw [tps_store_bytes (by omega), hT, ri_ze, hsn, tps_noLf_snoc, ite_eq_right hlf]
        · exact hO.trans (Out.widen (d := j) (out_store8 _ _ _) (by omega))
        · repeat refine tps_updK (by decide) hz0 ?_
          exact hfr
end

/-- The code `pem_spki` runs, and the header and footer it compares. -/
structure TpsCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M TPS tufPemSpkiCode
  strip : CodeIn M TPS_SP stripPrefixCode
  esl : CodeIn M TPS_ESL equalSameLengthCode
  mc : CodeIn M TPS_MC memcmpCode
  ms : CodeIn M TPS_MS memsetCode
  bdi : CodeIn M BDI base64DecodeIntoCode
  bcw : CodeIn M BCW copyFromSliceU8Code
  bms : CodeIn M BMS memcpyStubCode
  bmb : CodeIn M BMB memcpyBodyCode
  hdr : CodeIn M TPS_HDR tufPemHeaderData
  ftr : CodeIn M TPS_FTR tufPemFooterData

/-- What `pem_spki` returns in `a0` and `a1` and leaves in memory: memory
outside the 304 bytes at `s` and the 128 bytes at `out` as before, and for a
key, its bytes at `out`. -/
def TpsRes (M M' : Word → BitVec 8) (s out v0 v1 : Word) : Option Bytes → Prop
  | none => (∀ x, Sep x 1 s 304 → Sep x 1 out 128 → M' x = M x) ∧ v0 = 0
  | some bs => (∀ x, Sep x 1 s 304 → Sep x 1 out 128 → M' x = M x) ∧ v0 = out ∧
      v1 = BitVec.ofNat 32 bs.length ∧ memBytes M' out bs.length = bs

/-- The return to `ret` with `R` of memory, `a0`, and `a1`, and every
register outside `jClob` as in `g0`. -/
def TpsPost (ret : Word) (R : (Word → BitVec 8) → Word → Word → Prop) (g0 : Fin 32 → Word) : Post :=
  fun pc M' g => pc = ret ∧ R M' (g a0) (g a1) ∧ ∀ x, x ∉ jClob → g x = g0 x

/-- The five registers the prologue saves, in the frame at `F`. -/
def TpsSaved (Mf : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Prop :=
  memLoad32 Mf (F + 0xDC) = g0 ra ∧ memLoad32 Mf (F + 0xD8) = g0 8 ∧ memLoad32 Mf (F + 0xD4) = g0 9 ∧
    memLoad32 Mf (F + 0xD0) = g0 18 ∧ memLoad32 Mf (F + 0xCC) = g0 19

/-- The registers the epilogue restores. -/
abbrev tpsSv : List (Fin 32) := [ra, sp, 8, 9, 18, 19]

section
variable {M0 : Word → BitVec 8} {s out F : Word} {f g0 : Fin 32 → Word}

theorem tps_epi {R : (Word → BitVec 8) → Word → Word → Prop} {Mf : Word → BitVec 8} (hsp : f sp = F)
    (hS : TpsSaved Mf F g0) (hsp0 : g0 sp = F + BitVec.ofNat 32 0xE0) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ jClob ++ tpsSv → f x = g0 x)
    (hR : R Mf (f a0) (f a1)) :
    WP tufPemSpkiCode TPS (TpsPost (g0 ra) R g0) Mf 0x88 f := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := hS
  refine WP.lw tps_at_88 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xDC) (by decide)) ?_; wn
  refine WP.lw tps_at_8a (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xD8) (by decide)) ?_; wn
  refine WP.lw tps_at_8c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xD4) (by decide)) ?_; wn
  refine WP.lw tps_at_8e (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xD0) (by decide)) ?_; wn
  refine WP.lw tps_at_90 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0xCC) (by decide)) ?_; wn
  refine WP.aluImm tps_at_92 ?_; wn
  refine WP.ret tps_at_94 ⟨?_, ?_, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  · rsimp; exact hR
  refine frame_of (L2 := tpsSv) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]
  · rw [hsp, e5]

/-- The `None` tail at 0x2A. -/
theorem tps_none {Mf : Word → BitVec 8} (hsp : f sp = F) (hS : TpsSaved Mf F g0)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0xE0) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ jClob ++ tpsSv → f x = g0 x)
    (hOf : ∀ x, Sep x 1 s 304 → Sep x 1 out 128 → Mf x = M0 x) :
    WP tufPemSpkiCode TPS (TpsPost (g0 ra) (fun M' v0 v1 => TpsRes M0 M' s out v0 v1 none) g0) Mf 0x2A f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm tps_at_2a ?_; wn
  refine WP.jal tps_at_2c (by decide) ?_; wn
  refine tps_epi (by rsimp; exact hsp) hS hsp0 hret hal hz0 (tps_updK (by decide) hz0 hfr) ⟨hOf, ?_⟩
  rsimp; rw [hz, ev0]
end

theorem tps_toNat {a : Word} {c : Nat} (h : a.toNat + c < 2 ^ 32) : (a + BitVec.ofNat 32 c).toNat = a.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega), Nat.mod_eq_of_lt h]

theorem tps_sepS {s : Word} {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 2 ^ 32) : Sep s n (s + BitVec.ofNat 32 d) k := by
  have := sep_offsets s (c := 0) (n := n) (d := d) (k := k) (Or.inl (by omega)) (by omega) hd
  rwa [add_ofNat_zero] at this

theorem tps_sepR {a b : Word} {n k l : Nat} (h : Sep a n b k) (hl : l ≤ k) : Sep a n b l :=
  fun i hi j hj => h i hi j (by omega)

section
variable {M0 M1 : Word → BitVec 8} {s out F : Word} {f g0 : Fin 32 → Word}

/-- A saved register's slot, above the 284 bytes at `s` that the body
writes. -/
theorem tps_slot {Mf : Word → BitVec 8} {c : Nat} (hF : s + BitVec.ofNat 32 80 = F)
    (hso : Sep out 128 s 304) (hc1 : 0xCC ≤ c) (hc2 : c + 4 ≤ 0xE0)
    (h : ∀ x, Sep x 1 s 284 → Sep x 1 out 128 → Mf x = M1 x) :
    memLoad32 Mf (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by
    rw [← hF, add_ofNat_assoc, add_ofNat_assoc]
    exact h _ (tps_sepS (s := s) (n := 284) (d := 80 + (c + j)) (k := 1) (by omega) (by omega)).symm
      (hso.symm.sub (c := 80 + (c + j)) (l := 1) (by omega))

theorem tps_saved {Mf : Word → BitVec 8} (hF : s + BitVec.ofNat 32 80 = F)
    (hso : Sep out 128 s 304) (hS : TpsSaved M1 F g0)
    (h : ∀ x, Sep x 1 s 284 → Sep x 1 out 128 → Mf x = M1 x) : TpsSaved Mf F g0 :=
  ⟨(tps_slot (c := 0xDC) hF hso (by decide) (by decide) h).trans hS.1,
    (tps_slot (c := 0xD8) hF hso (by decide) (by decide) h).trans hS.2.1,
    (tps_slot (c := 0xD4) hF hso (by decide) (by decide) h).trans hS.2.2.1,
    (tps_slot (c := 0xD0) hF hso (by decide) (by decide) h).trans hS.2.2.2.1,
    (tps_slot (c := 0xCC) hF hso (by decide) (by decide) h).trans hS.2.2.2.2⟩

theorem tps_sltu {L : Nat} (hL : L ≤ 128) (o : Word) :
    aluEval .and (aluEval .sub 0 (aluEval .sltu (BitVec.ofNat 32 L) 0x81)) o = o := by
  have h1 : aluEval .sltu (BitVec.ofNat 32 L) 0x81 = 1 := by
    show (if (BitVec.ofNat 32 L).ult 0x81 then 1 else 0) = 1
    rw [show (BitVec.ofNat 32 L).ult 0x81 = true by
      show decide ((BitVec.ofNat 32 L).toNat < (0x81 : Word).toNat) = true
      rw [ofNat_tn (by omega), show (0x81 : Word).toNat = 0x81 from rfl]
      exact decide_eq_true (by omega)]
    rfl
  rw [h1]
  exact jones_and o

/-- From 0x96, after the loop kept the `text`: the bound check, the call to
`base64::decode_into`, and the return. -/
theorem tps_tail {Mk : Word → BitVec 8} {text : Bytes} (hsp : f sp = F) (h18 : f 18 = out)
    (h2 : f a2 = BitVec.ofNat 32 text.length) (hlen : text.length ≤ 192)
    (hT : memBytes Mk (F + BitVec.ofNat 32 4) text.length = text) (hS : TpsSaved M1 F g0)
    (hO1 : ∀ x, Sep x 1 s 304 → M1 x = M0 x) (hOk : Out M1 Mk s 284) (hc : TpsCode Mk)
    (hF : s + BitVec.ofNat 32 80 = F) (hal : s.toNat % 4 = 0) (hsw : s.toNat + 304 ≤ 0x40000000)
    (hso : Sep out 128 s 304) (how : out.toNat + 128 ≤ 0x40000000) (hsp0 : g0 sp = F + BitVec.ofNat 32 0xE0)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ jClob ++ tpsSv → f x = g0 x) :
    WP tufPemSpkiCode TPS (TpsPost (g0 ra) (fun M' v0 v1 => TpsRes M0 M' s out v0 v1 (pemDecode text)) g0)
      Mk 0x96 f := by
  have hFn : F.toNat = s.toNat + 80 := by rw [← hF]; exact tps_toNat (by omega)
  have halF : F.toNat % 4 = 0 := by omega
  have hFc : ∀ c, F + BitVec.ofNat 32 c = s + BitVec.ofNat 32 (80 + c) := fun c => by rw [← hF, add_ofNat_assoc]
  have hG : F + 0xFFFFFFB0 = s := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero s
  refine WP.zero fun hz => ?_
  refine WP.aluImm tps_at_96 ?_; wn
  refine WP.branch tps_at_9a (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [h2, hz, ev0] at eb
    change branchTaken .bgeu (BitVec.ofNat 32 text.length) (BitVec.ofNat 32 0xC1) = true at eb
    rw [br_bgeu (by omega) (by decide)] at eb
    exact not_dec_true eb (by omega)
  refine WP.aluImm tps_at_9e ?_; wn
  refine WP.aluImm tps_at_a0 ?_; wn
  refine WP.aluImm tps_at_a2 ?_; wn
  refine WP.alu tps_at_a6 ?_; wn
  refine WP.callB64 (sp0 := F) (res := F + BitVec.ofNat 32 0xC4) (t := F + BitVec.ofNat 32 4) (out := out)
    (n := text.length) (L := 128) tps_at_a8 tps_at_ac (by decide) (by decide) hc.bdi hc.bcw hc.bms hc.bmb
    (by rsimp; rw [ev_add, hsp]; rfl) (by rsimp; rw [ev_add, hsp]; rfl) (by rsimp; exact h2)
    (by rsimp; rw [ev0, h18]) (by rsimp) (by rsimp; exact hsp) halF (by omega) (by omega)
    (by rw [tps_toNat (by omega), hFn]; omega) (aligned_add halF (k := 0xC4) (by decide)) (by omega)
    (by rw [tps_toNat (by omega), hFn]; omega)
    (by rw [hG]; exact tps_sepR hso (by decide))
    (by rw [hG, hFc]; exact (tps_sepS (by decide) (by omega)).symm)
    (by rw [hG, hFc]; exact (tps_sepS (by decide) (by omega)).symm)
    (by rw [hFc]; exact hso.symm.sub (c := 84) (l := text.length) (by omega))
    (by rw [hFc]; exact hso.symm.sub (c := 276) (l := 8) (by omega))
    (by rw [hG]; exact lowSep (by omega) (by decide) (by decide))
    (lowSep (by omega) (by decide) (by decide))
    (lowSep (by rw [tps_toNat (by omega), hFn]; omega) (by decide) (by decide)) fun m5 hB => ?_
  unfold TpsB64Res at hB; rw [hT] at hB
  generalize m5.mem = M5 at hB
  obtain ⟨hok, herr, hfr5⟩ := hB
  have hM5 : ∀ x, Sep x 1 s 284 → Sep x 1 out 128 → M5 x = M1 x := fun x h1 h2 => by
    rw [hfr5 x (by rw [hG]; exact (tps_sepR h1 (by decide)).symm) h2.symm
      (by rw [hFc]; exact h1.symm.sub (c := 276) (l := 8) (by decide))]
    exact hOk x h1
  have hS5 := tps_saved hF hso hS hM5
  have hO5 : ∀ x, Sep x 1 s 304 → Sep x 1 out 128 → M5 x = M0 x := fun x h1 h2 => by
    rw [hM5 x (tps_sepR h1 (by decide)) h2]; exact hO1 x h1
  refine WP.zero fun hz5 => ?_
  refine WP.lbu tps_at_b0 ?_; wn
  refine WP.branch tps_at_b4 (fun eb => ?_) (fun eb => ?_) <;> wn
  · rsimp at eb; rw [hsp] at eb
    have hn : pemDecode text = none := by
      unfold pemDecode
      rw [ite_eq_left_of_eq_true _ _ (eq_true hlen)]
      rcases hd : base64Decode text with _ | bs
      · rfl
      · by_cases hb : bs.length ≤ 128
        · have r0 : M5 (F + 196) = 0 := (hok bs hd hb).1
          rw [r0] at eb; exact absurd eb (by decide)
        · exact ite_eq_right_of_eq_false _ _ (eq_false hb)
    rw [hn]
    exact tps_none (by rsimp; exact hsp) hS5 hsp0 hret halF hz0 (by keepz hz0) hO5
  · rsimp at eb; rw [hsp] at eb
    rcases hd : base64Decode text with _ | bs
    · have r1 : M5 (F + 196) = 1 := herr fun bs h => by rw [hd] at h; cases h
      rw [r1] at eb; exact absurd eb (by decide)
    by_cases hb' : 128 < bs.length
    · have r1 : M5 (F + 196) = 1 := herr fun bs' h => by rw [hd] at h; cases h; omega
      rw [r1] at eb; exact absurd eb (by decide)
    have hb : bs.length ≤ 128 := by omega
    obtain ⟨-, r1, r2⟩ := hok bs hd hb
    have r1' : memLoad32 M5 (F + 200) = BitVec.ofNat 32 bs.length := by
      rw [show (F + 200 : Word) = F + BitVec.ofNat 32 0xC4 + 4 from (add_ofNat_assoc F 0xC4 4).symm]
      exact r1
    have hn : pemDecode text = some bs := by
      unfold pemDecode; rw [ite_eq_left_of_eq_true _ _ (eq_true hlen), hd]
      exact ite_eq_left_of_eq_true _ _ (eq_true hb)
    rw [hn]
    refine WP.lw tps_at_b6 (by rsimp; rw [hsp]; exact aligned_add halF (k := 0xC8) (by decide)) ?_; wn
    refine WP.aluImm tps_at_b8 ?_; wn
    refine WP.alu tps_at_bc ?_; wn
    refine WP.alu tps_at_c0 ?_; wn
    refine WP.jal tps_at_c4 (by decide) ?_; wn
    refine tps_epi (by rsimp; exact hsp) hS5 hsp0 hret halF hz0 (by keepz hz0) ⟨hO5, ?_, ?_, r2⟩
    · rsimp; rw [hsp, r1', h18]; exact tps_sltu hb out
    · rsimp; rw [hsp, r1']
end

end C3.RV32

namespace C3.RV32

open C3.Image C3.Json

theorem tps_hdr_eq : tufPemHeaderData = ascii!"-----BEGIN PUBLIC KEY-----\n" := by decide
theorem tps_ftr_eq : tufPemFooterData = ascii!"-----END PUBLIC KEY-----\n" := by decide

section
variable {M : Word → BitVec 8} {p : Word} {n : Nat}

theorem tps_take27 (hn : 27 ≤ n) : (memBytes M p n).take 27 = memBytes M p 27 := by
  unfold memBytes
  rw [← List.map_take, List.take_range, Nat.min_eq_left hn]

theorem tps_tail25 (hn : 25 ≤ n) :
    (memBytes M p n).drop ((memBytes M p n).length - 25) = memBytes M (p + BitVec.ofNat 32 (n - 25)) 25 := by
  rw [memBytes_length, ← tuf_memBytes_drop_take (n := n) (h := n - 25) (l := 25) (by omega), List.take_of_length_le]
  rw [List.length_drop, memBytes_length]; omega

/-- With the header, the length, and the footer, the model decodes the body. -/
theorem tps_model_ok (hn : 52 ≤ n) (hh : memBytes M p 27 = tufPemHeaderData)
    (hf : memBytes M (p + BitVec.ofNat 32 (n - 25)) 25 = tufPemFooterData) :
    pemSpkiModel (memBytes M p n) = pemDecode (pemNoLf (memBytes M (p + BitVec.ofNat 32 27) (n - 52))) := by
  unfold pemSpkiModel
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [tps_take27 (by omega), hh, tps_hdr_eq],
    by rw [memBytes_length]; exact hn, by rw [tps_tail25 (by omega), hf, tps_ftr_eq]⟩), memBytes_length,
    tuf_memBytes_drop_take (by omega)]

theorem tps_model_hdr (h : ¬ (27 ≤ n ∧ memBytes M p 27 = tufPemHeaderData)) :
    pemSpkiModel (memBytes M p n) = none := by
  unfold pemSpkiModel
  refine ite_eq_right_of_eq_false _ _ (eq_false fun ⟨h1, h2, _⟩ => h ⟨by rw [memBytes_length] at h2; omega, ?_⟩)
  rw [memBytes_length] at h2
  rw [tps_take27 (by omega)] at h1
  rw [h1, tps_hdr_eq]

theorem tps_model_short (hn : n < 52) : pemSpkiModel (memBytes M p n) = none := by
  unfold pemSpkiModel
  refine ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, h2, _⟩ => ?_)
  rw [memBytes_length] at h2; omega

theorem tps_model_ftr (hn : 52 ≤ n) (hf : ¬ memBytes M (p + BitVec.ofNat 32 (n - 25)) 25 = tufPemFooterData) :
    pemSpkiModel (memBytes M p n) = none := by
  unfold pemSpkiModel
  refine ite_eq_right_of_eq_false _ _ (eq_false fun ⟨_, _, h3⟩ => hf ?_)
  rw [tps_tail25 (by omega)] at h3
  rw [h3, tps_ftr_eq]

end

theorem tps_codeIn {M M' : Word → BitVec 8} {s : Word} {k : Nat} {b : Word} {code : List Nat}
    (h : CodeIn M b code) (hO : Out M M' s k) (hs : s.toNat + k ≤ 0x40000000) (hb : 0x40000000 ≤ b.toNat)
    (hbl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn M' b code :=
  hO.codeIn h (lowSep hs hb hbl)

set_option maxRecDepth 100000 in
theorem TpsCode.of_out {M M' : Word → BitVec 8} {s : Word} {k : Nat} (h : TpsCode M) (hO : Out M M' s k)
    (hs : s.toNat + k ≤ 0x40000000) (hro : Sep s k (BitVec.ofNat 32 roWindowAddress) roWindowSize) :
    TpsCode M' :=
  ⟨tps_codeIn h.self hO hs (by decide) (by decide), tps_codeIn h.strip hO hs (by decide) (by decide),
    tps_codeIn h.esl hO hs (by decide) (by decide), tps_codeIn h.mc hO hs (by decide) (by decide),
    tps_codeIn h.ms hO hs (by decide) (by decide), tps_codeIn h.bdi hO hs (by decide) (by decide),
    tps_codeIn h.bcw hO hs (by decide) (by decide), tps_codeIn h.bms hO hs (by decide) (by decide),
    tps_codeIn h.bmb hO hs (by decide) (by decide),
    hO.codeIn h.hdr (tuf_sep_ro hro (by decide) (by decide)),
    hO.codeIn h.ftr (tuf_sep_ro hro (by decide) (by decide))⟩

theorem tps_beq_t {a b : Word} (h : branchTaken .beq a b = true) : a = b := beq_iff_eq.mp h

theorem tps_s0 {p : Word} {n : Nat} (h : 52 ≤ n) :
    aluEval .add (aluEval .add (BitVec.ofNat 32 (n - 27)) (p + BitVec.ofNat 32 27)) 0xFFFFFFE7 =
      p + BitVec.ofNat 32 (n - 25) := by
  rw [ev_add, ev_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFE7 : Word).toNat = 4294967271 from rfl]
  omega

theorem tps_sub : ∀ x, x ∈ tpsL → x ∈ jClob ++ tpsSv := by decide

section
variable {M0 : Word → BitVec 8} {s out p : Word} {n : Nat} {f : Fin 32 → Word}

set_option maxRecDepth 20000 in
theorem tps_wp (h0 : f a0 = p) (h1 : f a1 = BitVec.ofNat 32 n) (h2 : f a2 = out)
    (hsp : f sp = s + BitVec.ofNat 32 304) (hret : f ra &&& ~~~1 = f ra) (hal : s.toNat % 4 = 0)
    (hsw : s.toNat + 304 ≤ 0x40000000) (hro : Sep s 304 (BitVec.ofNat 32 roWindowAddress) roWindowSize)
    (hpw : p.toNat + n ≤ 0x40000000) (hSp : Sep s 304 p n) (how : out.toNat + 128 ≤ 0x40000000)
    (hso : Sep out 128 s 304) (hc : TpsCode M0) :
    WP tufPemSpkiCode TPS
      (TpsPost (f ra) (fun M' v0 v1 => TpsRes M0 M' s out v0 v1 (pemSpkiModel (memBytes M0 p n))) f) M0 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFF20 = s + 80 := by rw [hsp, ev_add, BitVec.add_assoc]; rfl
  refine WP.aluImm tps_at_0 ?_; wn
  rw [esp]
  generalize hF : s + 80 = F
  have hF' : s + BitVec.ofNat 32 80 = F := hF
  have hFn : F.toNat = s.toNat + 80 := by rw [← hF']; exact tps_toNat (by omega)
  have halF : F.toNat % 4 = 0 := by omega
  have hsp0 : f sp = F + BitVec.ofNat 32 0xE0 := by rw [hsp, ← hF', BitVec.add_assoc]; rfl
  have hFc : ∀ c, F + BitVec.ofNat 32 c = s + BitVec.ofNat 32 (80 + c) := fun c => by
    rw [← hF', add_ofNat_assoc]
  have hFN : ∀ {c}, c ≤ 224 → (F + BitVec.ofNat 32 c).toNat = s.toNat + 80 + c := fun hc => by
    rw [tps_toNat (by omega), hFn]
  have hFT : ∀ {c w : Nat}, c + w ≤ 224 → Sep (F + BitVec.ofNat 32 c) w TPS tufPemSpkiCode.length :=
    fun hc => lowSep (by rw [hFN (by omega)]; omega) (by decide) (by decide)
  -- The prologue saves five registers.
  refine WP.sw tps_at_2 (by rsimp; exact aligned_add halF (k := 0xDC) (by decide))
    (by rsimp; exact hFT (by decide)) ?_; wn
  refine WP.sw tps_at_4 (by rsimp; exact aligned_add halF (k := 0xD8) (by decide))
    (by rsimp; exact hFT (by decide)) ?_; wn
  refine WP.sw tps_at_6 (by rsimp; exact aligned_add halF (k := 0xD4) (by decide))
    (by rsimp; exact hFT (by decide)) ?_; wn
  refine WP.sw tps_at_8 (by rsimp; exact aligned_add halF (k := 0xD0) (by decide))
    (by rsimp; exact hFT (by decide)) ?_; wn
  refine WP.sw tps_at_a (by rsimp; exact aligned_add halF (k := 0xCC) (by decide))
    (by rsimp; exact hFT (by decide)) ?_; wn
  have hS1 : TpsSaved (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M0 (F + 220) (f ra))
      (F + 216) (f 8)) (F + 212) (f 9)) (F + 208) (f 18)) (F + 204) (f 19)) F f :=
    ⟨ld_skip 0xDC 0xCC (by decide) (by decide) (by decide) (ld_skip 0xDC 0xD0 (by decide) (by decide) (by decide)
      (ld_skip 0xDC 0xD4 (by decide) (by decide) (by decide) (ld_skip 0xDC 0xD8 (by decide) (by decide)
        (by decide) (memLoad32_store32_same _ _ _)))),
     ld_skip 0xD8 0xCC (by decide) (by decide) (by decide) (ld_skip 0xD8 0xD0 (by decide) (by decide) (by decide)
      (ld_skip 0xD8 0xD4 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _))),
     ld_skip 0xD4 0xCC (by decide) (by decide) (by decide) (ld_skip 0xD4 0xD0 (by decide) (by decide) (by decide)
      (memLoad32_store32_same _ _ _)),
     ld_skip 0xD0 0xCC (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _),
     memLoad32_store32_same _ _ _⟩
  have hO1 : Out M0 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M0 (F + 220) (f ra))
      (F + 216) (f 8)) (F + 212) (f 9)) (F + 208) (f 18)) (F + 204) (f 19)) s 304 :=
    ((((Out.upK (c := 300) (hFc 0xDC).symm (out_store32 _ _ _) (by decide)).trans
      (Out.upK (c := 296) (hFc 0xD8).symm (out_store32 _ _ _) (by decide))).trans
      (Out.upK (c := 292) (hFc 0xD4).symm (out_store32 _ _ _) (by decide))).trans
      (Out.upK (c := 288) (hFc 0xD0).symm (out_store32 _ _ _) (by decide))).trans
      (Out.upK (c := 284) (hFc 0xCC).symm (out_store32 _ _ _) (by decide))
  generalize memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M0 (F + 220) (f ra))
      (F + 216) (f 8)) (F + 212) (f 9)) (F + 208) (f 18)) (F + 204) (f 19) = M1 at hS1 hO1
  -- Everything after the prologue writes only below the saved registers.
  have hSk : ∀ {Mk : Word → BitVec 8}, Out M1 Mk s 284 → TpsSaved Mk F f := fun h =>
    tps_saved hF' hso hS1 fun x h1 _ => h x h1
  have hOk0 : ∀ {Mk : Word → BitVec 8}, Out M1 Mk s 284 → ∀ x, Sep x 1 s 304 → Sep x 1 out 128 → Mk x = M0 x :=
    fun h x h1 _ => (h x (tps_sepR h1 (by decide))).trans (hO1 x h1)
  have hCk : ∀ {Mk : Word → BitVec 8}, Out M1 Mk s 284 → TpsCode Mk := fun h =>
    hc.of_out (hO1.trans (h.mono (by decide))) hsw hro
  have hBk : ∀ {Mk : Word → BitVec 8} {c l : Nat}, c + l ≤ n → Out M1 Mk s 284 →
      memBytes Mk (p + BitVec.ofNat 32 c) l = memBytes M0 (p + BitVec.ofNat 32 c) l := fun hcl h =>
    (hO1.trans (h.mono (by decide))).bytes (hSp.subR hcl)
  have hc1 : TpsCode M1 := hCk fun _ _ => rfl
  have hR20 : F + 0xFFFFFFEC = s + BitVec.ofNat 32 60 := by rw [← hF', BitVec.add_assoc]; rfl
  have hs60 : (s + BitVec.ofNat 32 60).toNat = s.toNat + 60 := tps_toNat (by omega)
  -- The call to `strip_prefix` for the header.
  refine WP.alu tps_at_c ?_; wn
  refine WP.lui tps_at_e ?_; wn
  refine WP.aluImm tps_at_12 ?_; wn
  refine WP.aluImm tps_at_16 ?_; wn
  refine WP.callStrip (tb := TPS_SP) (s := p) (sl := n) (pre := TPS_HDR) (pl := 27) (r := s + BitVec.ofNat 32 60)
    tps_at_18 tps_at_1c (by decide) (by decide) (by decide) hc1.strip hc1.esl hc1.mc
    (by rsimp; exact h0) (by rsimp; exact h1) (by rsimp; try rfl) (by rsimp; (try rw [hz, ev0]); try rfl) (by omega)
    (by decide)
    (by rsimp; exact hR20) (by rsimp; exact halF)
    (lowSep (by rw [hs60]; omega) (by decide) (by decide)) (lowSep (by rw [hs60]; omega) (by decide) (by decide))
    (lowSep (by rw [hs60]; omega) (by decide) (by decide)) (hSp.sub (c := 60) (l := 20) (by decide))
    (tuf_sep_ro (hro.sub (c := 60) (l := 20) (by decide)) (by decide) (by decide))
    (lowSep (by rw [hs60]; omega) (by decide) (by decide)) fun m2 r0 r1 hO => ?_
  have hO2 : Out M1 m2.mem s 284 := Out.upK rfl hO (by decide)
  generalize m2.mem = M2 at r0 hO2
  have hH : memBytes M1 TPS_HDR 27 = tufPemHeaderData := tuf_codeIn_memBytes hc1.hdr (by decide)
  have hpn : ∀ {c}, c ≤ n → (p + BitVec.ofNat 32 c).toNat = p.toNat + c := fun hc => tps_toNat (by omega)
  have hc2 := hCk hO2
  by_cases hh : 27 ≤ n ∧ memBytes M1 p 27 = memBytes M1 TPS_HDR 27
  rotate_left
  · -- No header.
    rw [ite_eq_right_of_eq_false _ _ (eq_false hh)] at r0
    have hm : pemSpkiModel (memBytes M0 p n) = none := tps_model_hdr fun ⟨h27, he⟩ =>
      hh ⟨h27, by rw [hH, hO1.bytes (tps_sepR hSp h27), he]⟩
    rw [hm]
    refine WP.branch tps_at_20 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact tps_epi (by rsimp) (hSk hO2) hsp0 hret halF hz (by keepz hz) ⟨hOk0 hO2, by rsimp; exact r0⟩
    · exfalso; rsimp at eb; rw [r0] at eb; exact absurd eb (by decide)
  rw [ite_eq_left_of_eq_true _ _ (eq_true hh)] at r0
  obtain ⟨h27, hhe⟩ := hh
  have r1' := r1 h27
  refine WP.branch tps_at_20 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [r0] at eb
    have := congrArg BitVec.toNat (tps_beq_t eb)
    rw [hpn h27, show (0 : Word).toNat = 0 from rfl] at this
    omega
  refine WP.alu tps_at_22 ?_; wn
  refine WP.aluImm tps_at_24 ?_; wn
  refine WP.branch tps_at_26 (fun eb => ?_) (fun eb => ?_) <;> wn
  rotate_left
  · -- Too short for the footer.
    rsimp at eb; rw [r1', ev0] at eb
    change branchTaken .bgeu (BitVec.ofNat 32 (n - 27)) (BitVec.ofNat 32 25) = false at eb
    rw [br_bgeu (by omega) (by decide)] at eb
    have hn : n < 52 := by have := not_dec_false eb; omega
    rw [tps_model_short hn]
    exact tps_none (by rsimp) (hSk hO2) hsp0 hret halF hz (by keepz hz) (hOk0 hO2)
  rsimp at eb; rw [r1', ev0] at eb
  change branchTaken .bgeu (BitVec.ofNat 32 (n - 27)) (BitVec.ofNat 32 25) = true at eb
  rw [br_bgeu (by omega) (by decide)] at eb
  have h52 : 52 ≤ n := by have := not_dec_true eb; omega
  -- The call to `equal_same_length` for the footer.
  refine WP.alu tps_at_2e ?_; wn
  refine WP.aluImm tps_at_30 ?_; wn
  refine WP.lui tps_at_34 ?_; wn
  refine WP.aluImm tps_at_38 ?_; wn
  refine WP.aluImm tps_at_3c ?_; wn
  refine WP.alu tps_at_3e ?_; wn
  have hs8 : aluEval .add (aluEval .add (reg m2 a1) (aluEval .add 0 (reg m2 a0))) 4294967271 =
      p + BitVec.ofNat 32 (n - 25) := by
    rw [r1', ev0, r0]; exact tps_s0 h52
  have hR4 : F + 0xFFFFFFFC = s + BitVec.ofNat 32 76 := by rw [← hF', BitVec.add_assoc]; rfl
  have hs76 : (s + BitVec.ofNat 32 76).toNat = s.toNat + 76 := tps_toNat (by omega)
  refine WP.callEsl (tb := TPS_ESL) (q1 := p + BitVec.ofNat 32 (n - 25)) (q2 := TPS_FTR)
    (r := s + BitVec.ofNat 32 76) (l := 25) tps_at_40 tps_at_44 (by decide) (by decide) (by decide) hc2.esl hc2.mc
    (by rsimp; rw [ev0, hs8]) (by rsimp; try rfl) (by rsimp; (try rw [ev0]); try rfl) (by decide)
    (by rsimp; exact hR4) (by rsimp; exact halF)
    (lowSep (by rw [hs76]; omega) (by decide) (by decide)) (lowSep (by rw [hs76]; omega) (by decide) (by decide))
    ((hSp.sub (c := 76) (l := 4) (by decide)).subR (by omega))
    (tuf_sep_ro (hro.sub (c := 76) (l := 4) (by decide)) (by decide) (by decide))
    (lowSep (by rw [hs76]; omega) (by decide) (by decide)) fun m3 r3 hO => ?_
  have hO3 : Out M1 m3.mem s 284 := hO2.trans (Out.upK rfl hO (by decide))
  generalize m3.mem = M3 at r3 hO3
  have hFt : memBytes M2 TPS_FTR 25 = tufPemFooterData := tuf_codeIn_memBytes hc2.ftr (by decide)
  by_cases hft : memBytes M2 (p + BitVec.ofNat 32 (n - 25)) 25 = memBytes M2 TPS_FTR 25
  rotate_left
  · -- No footer.
    rw [ite_eq_right_of_eq_false _ _ (eq_false hft)] at r3
    have hm : pemSpkiModel (memBytes M0 p n) = none := tps_model_ftr h52 fun he =>
      hft (by rw [hFt, hBk (by omega) hO2, he])
    rw [hm]
    refine WP.branch tps_at_48 (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact tps_epi (by rsimp) (hSk hO3) hsp0 hret halF hz (by keepz hz) ⟨hOk0 hO3, by rsimp; exact r3⟩
    · exfalso; rsimp at eb; rw [r3] at eb; exact absurd eb (by decide)
  rw [ite_eq_left_of_eq_true _ _ (eq_true hft)] at r3
  refine WP.branch tps_at_48 (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb; rw [r3] at eb; exact absurd eb (by decide)
  have hm : pemSpkiModel (memBytes M0 p n) =
      pemDecode (pemNoLf (memBytes M0 (p + BitVec.ofNat 32 27) (n - 52))) :=
    tps_model_ok h52 (by rw [← hO1.bytes (tps_sepR hSp h27), hhe, hH])
      (by rw [← hBk (by omega) hO2, hft, hFt])
  rw [hm]
  -- `memset` of the text buffer.
  refine WP.aluImm tps_at_4a ?_; wn
  refine WP.aluImm tps_at_4c ?_; wn
  refine WP.aluImm tps_at_50 ?_; wn
  refine WP.aluImm tps_at_52 ?_; wn
  have hc3 := hCk hO3
  have hF4 : (F + BitVec.ofNat 32 4).toNat = s.toNat + 84 := hFN (by decide)
  refine WP.callMemsetT (tb := TPS_MS) (dst := F + BitVec.ofNat 32 4) (b := 0) (n := 192) tps_at_56 tps_at_5a
    (by decide) (by decide) (by decide) hc3.ms (by rsimp; (try rw [ev_add]); try rfl)
    (by rsimp; (try rw [ev0]); try rfl) (by rsimp; (try rw [ev0]); try rfl) (by omega)
    (lowSep (by rw [hF4]; omega) (by decide) (by decide)) (hFT (by decide)) fun m4 hm4 => ?_
  rw [hm4]
  have hO4 : Out M1 (fillBytes M3 (F + BitVec.ofNat 32 4) (BitVec.extractLsb' 0 8 (0 : Word)) 192) s 284 :=
    hO3.trans (Out.upK (hFc 4).symm (fun x hx => fillBytes_sep hx.symm (Nat.le_refl _)) (by decide))
  generalize fillBytes M3 (F + BitVec.ofNat 32 4) (BitVec.extractLsb' 0 8 (0 : Word)) 192 = M4 at hO4
  rw [← hBk (c := 27) (l := n - 52) (by omega) hO4]
  -- The filter loop.
  refine WP.aluImm tps_at_5e ?_; wn
  refine WP.aluImm tps_at_60 ?_; wn
  refine WP.alu tps_at_62 ?_; wn
  refine tps_loop (Mm := M4) (q := p + BitVec.ofNat 32 27) (T := F + BitVec.ofNat 32 4) (bl := n - 52)
    (by rw [hpn (by omega)]; omega) (by rw [hF4]; omega)
    (by rw [hFc]; exact (hSp.symm.sub (c := 27) (l := n - 52) (by omega)).subR (by decide))
    (hFT (by decide)) ?h8 ?h19 ?ha0 ?hz0 ?Kok ?Kov (n - 52) 0 0 M4 _ (by omega) ?h3 ?h9 ?h2 rfl (by decide) rfl
    (fun _ _ => rfl) (fun _ _ => rfl)
  case h8 => rsimp; rw [hs8, add_ofNat_assoc, show 27 + (n - 52) = n - 25 by omega]
  case h19 => rsimp; (try rw [ev_add]); try rfl
  case ha0 => rsimp; (try rw [ev0]); try rfl
  case hz0 => rsimp; try exact hz
  case h3 => rsimp; rw [ev0, ev0, r0, add_ofNat_zero]
  case h9 => rsimp; rw [ev0, r0, add_ofNat_zero]
  case h2 => rsimp; (try rw [ev0]); try rfl
  case Kov =>
    intro g Mk hov hOk hfrk
    have hOk' : Out M1 Mk s 284 := hO4.trans (Out.upK (hFc 4).symm hOk (by decide))
    have hfr' : ∀ x, x ∉ jClob ++ tpsSv → g x = f x := by
      refine fun x hx => (hfrk x fun hm => hx (tps_sub x hm)).trans ?_
      revert x; keepz hz
    rw [show pemDecode (pemNoLf (memBytes M4 (p + 27#32) (n - 52))) = none by
      unfold pemDecode; exact ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact tps_none (by rw [hfrk sp (by decide)]; rsimp) (hSk hOk') hsp0 hret halF hz hfr' (hOk0 hOk')
  case Kok =>
    intro g Mk hg2 hlen hTk hOk hfrk
    have hOk' : Out M1 Mk s 284 := hO4.trans (Out.upK (hFc 4).symm hOk (by decide))
    have hfr' : ∀ x, x ∉ jClob ++ tpsSv → g x = f x := by
      refine fun x hx => (hfrk x fun hm => hx (tps_sub x hm)).trans ?_
      revert x; keepz hz
    exact tps_tail (by rw [hfrk sp (by decide)]; rsimp) (by rw [hfrk 18 (by decide)]; rsimp; rw [ev0, h2]) hg2
      hlen hTk hS1 hO1 hOk' (hCk hOk') hF' hal hsw hso how hsp0 hret hz hfr'
end

/-- `tuf::pem_spki` from its entry, with the PEM text the `n` bytes at `p` in
`a0` and `a1`, the 128-byte output buffer at `out` in `a2`, and the stack the
304 bytes below `sp` (its own 224-byte frame and the 80 bytes that
`base64::decode_into` uses). It returns to `ra` with `pemSpkiModel` of the
text: for a key, `out` in `a0`, the key's length in `a1`, and the key at
`out`; otherwise 0 in `a0`. Memory outside the stack and the 128 bytes at
`out` is as before, and so is every register outside `jClob`. The stack and
`out` lie below the code, the stack is apart from the read-only data window,
`out`, and the text. -/
theorem tufPemSpki_correct (m : Machine) {retAddr out s p : Word} {n : Nat}
    (hc : TpsCode m.mem) (hpc : m.pc = TPS) (ha0 : reg m a0 = p) (ha1 : reg m a1 = BitVec.ofNat 32 n)
    (ha2 : reg m a2 = out) (hsp : reg m sp = s + BitVec.ofNat 32 304) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hal : s.toNat % 4 = 0) (hsw : s.toNat + 304 ≤ 0x40000000)
    (hro : Sep s 304 (BitVec.ofNat 32 roWindowAddress) roWindowSize) (hpw : p.toNat + n ≤ 0x40000000)
    (hSp : Sep s 304 p n) (how : out.toNat + 128 ≤ 0x40000000) (hso : Sep out 128 s 304) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      TpsRes m.mem m'.mem s out (reg m' a0) (reg m' a1) (pemSpkiModel (memBytes m.mem p n)) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (tps_wp ha0 ha1 ha2 hsp (by rw [hra]; exact hret) hal hsw hro hpw
    hSp how hso hc) (by decide) hc.self hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32

/-! ## The specification's `pemSpki` -/

namespace C3.Json

theorem tps_bind {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem tps_group_len {c0 c1 c2 c3 pad : Nat} {g : Bytes}
    (h : b64Group c0 c1 c2 c3 pad = some g) : g.length = 3 - pad := by
  unfold b64Group at h
  obtain ⟨_, -, h⟩ := tps_bind h
  obtain ⟨_, -, h⟩ := tps_bind h
  dsimp only at h
  split at h <;> obtain ⟨_, -, h⟩ := tps_bind h <;> (try dsimp only at h) <;>
    split at h <;> obtain ⟨_, -, h⟩ := tps_bind h <;> obtain ⟨_, -, h⟩ := tps_bind h <;>
    cases h <;> rw [List.length_take] <;> simp only [List.length_cons, List.length_nil] <;> omega

theorem tps_dec_len : ∀ (x : Bytes) {bs : Bytes}, base64Decode x = some bs →
    3 * (x.length / 4) ≤ bs.length + 2
  | [], _, h => by unfold base64Decode at h; cases h; decide
  | [_], _, h => by unfold base64Decode at h; cases h
  | [_, _], _, h => by unfold base64Decode at h; cases h
  | [_, _, _], _, h => by unfold base64Decode at h; cases h
  | [c0, c1, c2, c3], _, h => by
    unfold base64Decode at h
    have := tps_group_len h
    simp only [List.length_cons, List.length_nil]
    split at this <;> (try split at this) <;> omega
  | c0 :: c1 :: c2 :: c3 :: r0 :: rest, _, h => by
    unfold base64Decode at h
    obtain ⟨g, hg, h⟩ := tps_bind h
    obtain ⟨r, hr, h⟩ := tps_bind h
    cases h
    have h1 := tps_group_len hg
    have h2 := tps_dec_len (r0 :: rest) hr
    simp only [List.length_cons, List.length_append] at h1 h2 ⊢
    omega

theorem tps_hdr_len : (ascii!"-----BEGIN PUBLIC KEY-----\n").length = 27 := by decide
theorem tps_ftr_len : (ascii!"-----END PUBLIC KEY-----\n").length = 25 := by decide

theorem tps_spec_eq (pem : Bytes) :
    pemSpki pem =
      if pem.take 27 = ascii!"-----BEGIN PUBLIC KEY-----\n" ∧ 52 ≤ pem.length ∧
          pem.drop (pem.length - 25) = ascii!"-----END PUBLIC KEY-----\n" then
        base64Decode (((pem.drop 27).take (pem.length - 52)).filter (· != 0x0A))
      else none := by
  unfold pemSpki readExpect
  rw [tps_hdr_len]
  rcases Decidable.em (pem.take 27 = ascii!"-----BEGIN PUBLIC KEY-----\n") with h1 | h1
  · have hl : 27 ≤ pem.length := by
      have := congrArg List.length h1
      rw [List.length_take, tps_hdr_len] at this
      omega
    have e1 : (pem.take 27 == ascii!"-----BEGIN PUBLIC KEY-----\n" && decide (27 ≤ pem.length)) =
        true := by
      rw [beq_iff_eq.mpr h1, decide_eq_true hl]; rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true e1)]
    show (require _ >>= fun _ => _) = _
    rw [List.length_drop, tps_ftr_len]
    rcases Decidable.em (52 ≤ pem.length ∧ pem.drop (pem.length - 25) = ascii!"-----END PUBLIC KEY-----\n") with h2 | h2
    · have e2 : (ascii!"-----END PUBLIC KEY-----\n").isSuffixOf (pem.drop 27) = true := by
        rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop, List.length_drop, tps_ftr_len,
          List.drop_drop]
        rw [show 27 + (pem.length - 27 - 25) = pem.length - 25 by omega]
        exact h2.2.symm
      rw [e2, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h2⟩)]
      rw [show pem.length - 27 - 25 = pem.length - 52 by omega]
      rfl
    · have e2 : (ascii!"-----END PUBLIC KEY-----\n").isSuffixOf (pem.drop 27) = false := by
        cases e : (ascii!"-----END PUBLIC KEY-----\n").isSuffixOf (pem.drop 27)
        · rfl
        · exfalso
          rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop, List.length_drop, tps_ftr_len,
            List.drop_drop] at e
          have hlen := congrArg List.length e
          rw [tps_ftr_len, List.length_drop] at hlen
          apply h2
          refine ⟨by omega, ?_⟩
          rw [e, show 27 + (pem.length - 27 - 25) = pem.length - 25 by omega]
      rw [e2, ite_eq_right_of_eq_false _ _ (eq_false (fun h => h2 ⟨h.2.1, h.2.2⟩))]
      rfl
  · have e1 : (pem.take 27 == ascii!"-----BEGIN PUBLIC KEY-----\n" && decide (27 ≤ pem.length)) =
        false := by
      cases e : (pem.take 27 == ascii!"-----BEGIN PUBLIC KEY-----\n")
      · rfl
      · exact absurd (beq_iff_eq.mp e) h1
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [e1]; decide)),
      ite_eq_right_of_eq_false _ _ (eq_false (fun h => h1 h.1))]
    rfl

theorem tps_dec_small {text bs : Bytes} (h : base64Decode text = some bs) (hb : bs.length ≤ 120) :
    pemDecode text = some bs := by
  have := tps_dec_len text h
  unfold pemDecode
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h]
  exact ite_eq_left_of_eq_true _ _ (eq_true (by omega))

theorem tps_dec_some {text bs : Bytes} (h : pemDecode text = some bs) : base64Decode text = some bs := by
  unfold pemDecode at h
  split at h
  · split at h
    · rename_i bs' e
      rw [e]
      split at h
      · exact h
      · cases h
    · cases h
  · cases h

/-- Every key that `pem_spki` returns is the specification's `pemSpki`. -/
theorem pemSpkiModel_sound {pem bs : Bytes} (h : pemSpkiModel pem = some bs) :
    pemSpki pem = some bs := by
  rw [tps_spec_eq]
  unfold pemSpkiModel at h
  split at h
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
    exact tps_dec_some h
  · cases h

/-- `pem_spki` returns every key of at most 120 bytes that the specification's
`pemSpki` decodes. Both SPKI shapes that `decodeKey` accepts are at most 120
bytes. -/
theorem pemSpkiModel_complete {pem bs : Bytes} (h : pemSpki pem = some bs) (hb : bs.length ≤ 120) :
    pemSpkiModel pem = some bs := by
  rw [tps_spec_eq] at h
  unfold pemSpkiModel
  split at h
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
    exact tps_dec_small h hb
  · cases h

theorem tps_spki_len {pfx s pt : Bytes} {len : Nat} (h : spkiPoint pfx len s = some pt) :
    s.length = pfx.length + len := by
  unfold spkiPoint readExpect at h
  obtain ⟨_, h1, h⟩ := tps_bind h
  obtain ⟨_, h2, h⟩ := tps_bind h
  cases h
  split at h1
  · rename_i hc
    cases h1
    unfold require at h2
    split at h2
    · rename_i hl
      have := beq_iff_eq.mp hl
      have := (Bool.and_eq_true _ _).mp hc
      have := of_decide_eq_true this.2
      rw [List.length_drop] at *
      omega
    · cases h2
  · cases h1

/-- Through `spkiPoint`, as `decodeKey` uses it, `pem_spki` and the
specification's `pemSpki` agree on every input when the SPKI is at most 120
bytes. -/
theorem pemSpkiModel_spkiPoint (pem pfx : Bytes) (len : Nat) (hl : pfx.length + len ≤ 120) :
    (pemSpkiModel pem >>= spkiPoint pfx len) = (pemSpki pem >>= spkiPoint pfx len) := by
  cases hm : pemSpkiModel pem with
  | some bs => rw [pemSpkiModel_sound hm]
  | none =>
    cases hs : pemSpki pem with
    | none => rfl
    | some bs =>
      show none = spkiPoint pfx len bs
      cases hp : spkiPoint pfx len bs with
      | none => rfl
      | some pt =>
        have := tps_spki_len hp
        rw [pemSpkiModel_complete hs (by omega)] at hm
        cases hm

theorem pemSpkiModel_p256 (pem : Bytes) :
    (pemSpkiModel pem >>= spkiPoint p256SpkiPrefix 65) = (pemSpki pem >>= spkiPoint p256SpkiPrefix 65) :=
  pemSpkiModel_spkiPoint pem _ _ (by decide)

theorem pemSpkiModel_p384 (pem : Bytes) :
    (pemSpkiModel pem >>= spkiPoint p384SpkiPrefix 97) = (pemSpki pem >>= spkiPoint p384SpkiPrefix 97) :=
  pemSpkiModel_spkiPoint pem _ _ (by decide)

end C3.Json
