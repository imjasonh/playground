#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/PointAdd.lean, the proof of the compiled P-256
point addition, from the decoded instructions in PointDecode.lean.

The body between the prologue and the epilogue is argument setup (`addi`,
`mv`, `li`, `lui`) and 46 calls. This script simulates the argument
registers symbolically to find each call's result slot and operands, then
emits one step or call lemma from PointEnv.lean per instruction, names each
call's result after its field operation, and carries every frame slot's
value across the calls while a later call still reads it.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', 'C3BootProofs', 'Proofs') + os.sep
OUT = sys.argv[1] if len(sys.argv) > 1 else ROOT + 'PointAdd.lean'

REGNUM = {'x0': 0, 'ra': 1, 'sp': 2, 'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13, 'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17}
NAME = {v: k for k, v in REGNUM.items()}


def decode(text, prefix, code):
    out = {}
    pat = r'theorem %s_at_(\w+) : fetchRel %s (0x[0-9A-F]+) = some \((.*), (\d)\) := by decide' % (prefix, code)
    for m in re.finditer(pat, text):
        out[int(m.group(2), 16)] = (m.group(3), int(m.group(4)))
    return out


def rnum(s):
    m = re.match(r'\((\d+) : Fin 32\)', s)
    return int(m.group(1)) if m else REGNUM[s]


def rname(n):
    return NAME.get(n, f'({n} : Fin 32)')


src = open(ROOT + 'PointDecode.lean').read()
PA = decode(src, 'pa', 'pointAddCode')
offs = sorted(PA)
G = "sp0 + 0xFFFFFDC0"
CALLEES = {0xE838: 'mul', 0xEF8A: 'add', 0xF0AC: 'sub', 0xF290: 'dbl', 0x1D168: 'cpy'}
OPF = {'mul': 'fm', 'add': 'fa', 'sub': 'fs', 'dbl': 'fd'}
KEPT = {2, 8, 9, 18, 19, 20, 21}


def h(x):
    return f"0x{x:X}"


def lit(s):
    return int(s, 16)


def vstr(v):
    t = v[0]
    if t == 'G':
        return G
    if t == 'slot':
        return f"{G} + BitVec.ofNat 32 {h(v[1])}"
    if t in ('lhs', 'rhs'):
        return v[0] if v[1] == 0 else f"{v[0]} + BitVec.ofNat 32 {h(v[1])}"
    if t == 'b':
        return "bAddr"
    if t == 'imm':
        return h(v[1])
    raise Exception(v)


def pdst(c):
    assert 4 <= c and c + 32 <= 0x224 and c % 4 == 0, c
    return "⟨by decide, by decide, by decide⟩"


# ---------- pass 1: symbolic simulation, collect calls ----------
def body():
    for o in offs:
        if 0x22 <= o < 0x2BC:
            yield o


def simulate():
    kv = {2: ('G',), 9: ('rhs', 0), 20: ('lhs', 0)}
    av = {}
    calls = []
    skip = set()
    for o in body():
        if o in skip:
            continue
        ins, ln = PA[o]
        kd = ins.split()[0]
        if kd == '.auipc':
            imm = lit(ins.split()[2])
            jins, _ = PA[o + 4]
            joff = lit(jins.split()[3])
            tgt = (o + imm + joff) % 2 ** 32
            kind = CALLEES[tgt]
            calls.append((o, kind, av.get(10), av.get(11), av.get(12)))
            av = {}
            skip.add(o + 4)
            continue
        if kd == '.aluImm':
            m = re.match(r'\.aluImm \.add (\(\d+ : Fin 32\)|\S+) (\(\d+ : Fin 32\)|\S+) (0x[0-9A-F]+)', ins)
            rd, rs, imm = rnum(m.group(1)), rnum(m.group(2)), lit(m.group(3))
            if rs == 2:
                val = ('slot', imm)
            elif rs == 0:
                val = ('imm', imm)
            else:
                base = kv[rs] if rs in KEPT else av[rs]
                if base[0] in ('lhs', 'rhs'):
                    val = (base[0], base[1] + imm)
                elif base[0] == 'imm':
                    val = ('imm', (base[1] + imm) % 2 ** 32)
                    if val[1] == 0x3FCC4368:
                        val = ('b',)
                else:
                    raise Exception(ins)
        elif kd == '.alu':
            m = re.match(r'\.alu \.add (\(\d+ : Fin 32\)|\S+) x0 (\(\d+ : Fin 32\)|\S+)', ins)
            rd, rs = rnum(m.group(1)), rnum(m.group(2))
            val = kv[rs] if rs in KEPT else av[rs]
        elif kd == '.lui':
            m = re.match(r'\.lui (\(\d+ : Fin 32\)|\S+) (0x[0-9A-F]+)', ins)
            rd, val = rnum(m.group(1)), ('imm', lit(m.group(2)))
        else:
            raise Exception(ins)
        if rd in KEPT:
            kv[rd] = val
        else:
            av[rd] = val
    return calls


CALLS = simulate()
assert len(CALLS) == 46, len(CALLS)


def reads(c):
    o, kind, a0, a1, a2 = c
    srcs = [a1] if kind in ('dbl', 'cpy') else [a1, a2]
    return [s[1] for s in srcs if s[0] == 'slot']


LIVE = []  # slots live after call j
for j in range(len(CALLS)):
    live = set()
    for c in range(4, 0x224, 4):
        for c2 in CALLS[j + 1:]:
            if c in reads(c2):
                live.add(c)
                break
            if c2[1] != 'cpy' and c2[2] == ('slot', c):
                break
    LIVE.append(live)

# ---------- pass 2: emit ----------
L = []
w = L.append
INPUTS = {('lhs', 0): 'X1', ('lhs', 0x20): 'Y1', ('lhs', 0x40): 'Z1',
          ('rhs', 0): 'X2', ('rhs', 0x20): 'Y2', ('rhs', 0x40): 'Z2'}


def sep_in(v):
    if v[0] == 'b':
        return "env.sK"
    s = 'env.sL' if v[0] == 'lhs' else 'env.sR'
    if v[1] == 0:
        return f"(sep_base0 ({s}.sub (c := 0) (l := 32) (by decide)))"
    return f"({s}.sub (c := {h(v[1])}) (l := 32) (by decide))"


def psrc(v):
    if v[0] == 'slot':
        return f"(psrc_slot env {pdst(v[1])})"
    if v[0] == 'b':
        return "(psrc_b env)"
    fn = 'pL' if v[0] == 'lhs' else 'pR'
    return f"{fn}{v[1]:X}"


k = 0          # step index; n{k}, I{k}
M = 'Ms'       # current memory name
W = 0
vname = 'V0'
vj = 0         # V counter
kvp = {}       # kept reg -> (sym, proof of V r = val)
av = {}        # a-reg -> (sym, proof of reg n_k r = val)
slots = {}     # slot -> (valname, proof limbVal(...) = val, lt proof)
outs = {}      # lhs coord -> (valname, proof)
steps = []
vals = 0


def kreg(r):
    return f"((I{k}.keep {rname(r)} rfl).trans {kvp[r][1]})"


def regp(r):
    if r in KEPT:
        return kreg(r)
    return av[r][1]


def regsym(r):
    return kvp[r][0] if r in KEPT else av[r][0]


def operand(v):
    """(value-name, proof of limbVal (wordsAt M_k a 8) = name, lt-proof)"""
    if v[0] == 'slot':
        return slots[v[1]]
    if v[0] == 'b':
        return ('bMont', f"((congrArg limbVal (I{k-1}.inp env.sK)).trans env.bconst)", 'bMont_lt')
    nm = INPUTS[v]
    return (nm, f"((congrArg limbVal (I{k-1}.inp {sep_in(v)})).trans h{nm})", f"l{nm}")


w("  obtain ⟨n0, Ms, c0, I0, psp, ps1, ps4, pk, psl⟩ := pa_pro m env hpc ha0 ha1 hsp")
w("  obtain ⟨V0, hV0⟩ : ∃ V, reg n0 = V := ⟨_, rfl⟩")
w("  rw [hV0] at I0")
w("  have vsp0 : V0 sp = sp0 + 0xFFFFFDC0 := by rw [← hV0]; exact psp")
w("  have vs1_0 : V0 (9 : Fin 32) = rhs := by rw [← hV0]; exact ps1")
w("  have vs4_0 : V0 (20 : Fin 32) = lhs := by rw [← hV0]; exact ps4")
kvp = {2: (('G',), 'vsp0'), 9: (('rhs', 0), 'vs1_0'), 20: (('lhs', 0), 'vs4_0')}
for (side, off), nm in INPUTS.items():
    addr = side if off == 0 else f"{side} + {h(off)}"
    w(f"  obtain ⟨{nm}, h{nm}⟩ : ∃ v, limbVal (wordsAt m.mem ({addr}) 8) = v := ⟨_, rfl⟩")
    w(f"  have l{nm} : {nm} < p256 := by rw [← h{nm}]; exact h{nm.lower()}")
for side, fn in (('lhs', 'pL'), ('rhs', 'pR')):
    w(f"  have {fn}0 : PSrc sp0 {side} := by")
    w(f"    have := psrc_{side} env 0 (by decide) (by decide); rwa [add_ofNat_zero] at this")
    for off in (0x20, 0x40):
        w(f"  have {fn}{off:X} := psrc_{side} env {h(off)} (by decide) (by decide)")

ci = 0
skip = set()
for o in body():
    if o in skip:
        continue
    ins, ln = PA[o]
    kd = ins.split()[0]
    nxt = o + ln
    if kd == '.auipc':
        jo, kind, a0v, a1v, a2v = CALLS[ci]
        assert jo == o
        skip.add(o + 4)
        k += 1
        hb = f"(by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)"
        if kind == 'cpy':
            assert a0v[0] == 'lhs' and a0v[1] == W and a1v[0] == 'slot' and a2v == ('imm', 0x20), (a0v, a1v, a2v)
            a0p = av[10][1] if W else f"({av[10][1]}.trans (add_ofNat_zero lhs).symm)"
            w(f"  obtain ⟨n{k}, M{k}, d{k}, I{k}, f{k}, w{k}⟩ := pa_cpy (d := {h(a1v[1])}) env I{k-1} (k := {h(W)}) (by decide) (by decide)")
            w(f"    pa_at_{o:x} pa_at_{o+4:x} {hb} (by decide) {pdst(a1v[1])}")
            w(f"    {a0p}")
            w(f"    {av[11][1]}")
            w(f"    {av[12][1]}")
            sv, sp_, sl = slots[a1v[1]]
            newouts = {}
            for kk, (nm, p) in outs.items():
                newouts[kk] = (nm, f"((congrArg limbVal (lhs_keep_cpy (k := {h(W)}) (by decide) (by decide) f{k})).trans {p})")
            newouts[W] = (sv, f"((congrArg limbVal w{k}).trans {sp_})")
            outs = newouts
            newslots = {}
            for c in LIVE[ci]:
                nm, p, lt = slots[c]
                newslots[c] = (nm, f"((congrArg limbVal (slot_keep_cpy env (k := {h(W)}) (by decide) f{k} {pdst(c)})).trans {p})", lt)
            slots = newslots
            W += 32
        else:
            assert a0v[0] == 'slot'
            d = a0v[1]
            A = operand(a1v)
            line = (f"  obtain ⟨n{k}, M{k}, d{k}, I{k}, f{k}, w{k}⟩ := pa_{kind} (d := {h(d)}) env I{k-1} (by decide) {kvp[2][1]}\n"
                    f"    pa_at_{o:x} pa_at_{o+4:x} {hb} (by decide) {pdst(d)}\n"
                    f"    {av[10][1]}\n"
                    f"    {psrc(a1v)} {av[11][1]}")
            if kind != 'dbl':
                B = operand(a2v)
                line += f"\n    {psrc(a2v)} {av[12][1]}"
                line += f"\n    {A[1]} {A[2]}\n    {B[1]} {B[2]}"
                expr = f"{OPF[kind]} {A[0]} {B[0]}"
            else:
                line += f"\n    {A[1]} {A[2]}"
                expr = f"{OPF[kind]} {A[0]}"
            w(line)
            vals += 1
            v = f"v{vals}"
            w(f"  obtain ⟨{v}, h{v}⟩ : ∃ v, {expr} = v := ⟨_, rfl⟩")
            ltname = f"l{v}"
            w(f"  have {ltname} : {v} < p256 := h{v} ▸ {OPF[kind]}_lt _{' _' if kind != 'dbl' else ''}")
            newouts = {}
            for kk, (nm, p) in outs.items():
                newouts[kk] = (nm, f"((congrArg limbVal (lhs_keep env f{k} {pdst(d)} (k := {h(kk)}) (by decide))).trans {p})")
            outs = newouts
            newslots = {}
            for c in LIVE[ci]:
                if c == d:
                    continue
                nm, p, lt = slots[c]
                newslots[c] = (nm, f"((congrArg limbVal (slot_keep f{k} {pdst(d)} {pdst(c)} (by decide))).trans {p})", lt)
            if d in LIVE[ci]:
                newslots[d] = (v, f"(w{k}.trans h{v})", ltname)
            slots = newslots
            # consolidate long proof chains into named facts
        for c in list(slots):
            nm, p, lt = slots[c]
            w(f"  have s{k}_{c:x} : limbVal (wordsAt M{k} ({G} + BitVec.ofNat 32 {h(c)}) 8) = {nm} := {p}")
            slots[c] = (nm, f"s{k}_{c:x}", lt)
        for kk in list(outs):
            nm, p = outs[kk]
            w(f"  have o{k}_{kk:x} : limbVal (wordsAt M{k} (lhs + BitVec.ofNat 32 {h(kk)}) 8) = {nm} := {p}")
            outs[kk] = (nm, f"o{k}_{kk:x}")
        M = f"M{k}"
        av = {}
        steps.append(f"d{k}")
        ci += 1
        continue
    k += 1
    if kd == '.aluImm':
        m = re.match(r'\.aluImm \.add (\(\d+ : Fin 32\)|\S+) (\(\d+ : Fin 32\)|\S+) (0x[0-9A-F]+)', ins)
        rd, rs, imm = rnum(m.group(1)), rnum(m.group(2)), lit(m.group(3))
        if rd in KEPT:
            base = regsym(rs)
            vj += 1
            newV = f"V{vj}"
            w(f"  obtain ⟨n{k}, d{k}, I{k}', e{k}, o{k}⟩ := pa_addiK env I{k-1} (by decide) pa_at_{o:x} (off' := {h(nxt)}) (by decide) (by decide)")
            k -= 1
            rsp = regp(rs)
            k += 1
            w(f"  obtain ⟨{newV}, h{newV}⟩ : ∃ V, upd {vname} {rname(rd)} (reg n{k-1} {rname(rs)} + {h(imm)}) = V := ⟨_, rfl⟩")
            w(f"  rw [h{newV}] at I{k}'")
            w(f"  have I{k} := I{k}'")
            if base[0] in ('lhs', 'rhs'):
                val = (base[0], base[1] + imm)
            else:
                assert base[0] == 'imm'
                val = ('imm', (base[1] + imm) % 2 ** 32)
                if val[1] == 0x3FCC4368:
                    val = ('b',)
            nk = {}
            for r, (sym, p) in kvp.items():
                if r == rd:
                    continue
                nk[r] = (sym, f"(by rw [← h{newV}, upd_ne (by decide) (by decide)]; exact {p})")
            nk[rd] = (val, f"(by rw [← h{newV}, upd_same (by decide), {rsp}]; rfl)")
            vname = newV
            kvp = nk
            for r in list(kvp):
                sym, p = kvp[r]
                w(f"  have vk{k}_{r} : {vname} {rname(r)} = {vstr(sym)} := {p}")
                kvp[r] = (sym, f"vk{k}_{r}")
            av = {r: (sym, f"((o{k} {rname(r)} (by decide)).trans {p})") for r, (sym, p) in av.items()}
        else:
            w(f"  obtain ⟨n{k}, d{k}, I{k}, e{k}, o{k}⟩ := pa_addi env I{k-1} (by decide) pa_at_{o:x} (off' := {h(nxt)}) (by decide) rfl")
            if rs == 2:
                val = ('slot', imm)
                k -= 1
                p0 = kreg(2)
                k += 1
                p = f"(e{k}.trans (by rw [{p0}]; rfl))"
            elif rs == 0:
                val = ('imm', imm)
                p = f"(e{k}.trans (by show reg n{k-1} 0 + {h(imm)} = {h(imm)}; rw [I{k-1}.st.zero]; rfl))"
            else:
                raise Exception(ins)
            na = {r: (sym, f"((o{k} {rname(r)} (by decide)).trans {pp})") for r, (sym, pp) in av.items() if r != rd}
            na[rd] = (val, p)
            av = na
    elif kd == '.alu':
        m = re.match(r'\.alu \.add (\(\d+ : Fin 32\)|\S+) x0 (\(\d+ : Fin 32\)|\S+)', ins)
        rd, rs = rnum(m.group(1)), rnum(m.group(2))
        assert rd not in KEPT and rs in KEPT
        w(f"  obtain ⟨n{k}, d{k}, I{k}, e{k}, o{k}⟩ := pa_mv env I{k-1} (by decide) pa_at_{o:x} (off' := {h(nxt)}) (by decide) rfl")
        k -= 1
        p0 = kreg(rs)
        k += 1
        na = {r: (sym, f"((o{k} {rname(r)} (by decide)).trans {pp})") for r, (sym, pp) in av.items() if r != rd}
        na[rd] = (kvp[rs][0], f"(e{k}.trans {p0})")
        av = na
    elif kd == '.lui':
        m = re.match(r'\.lui (\(\d+ : Fin 32\)|\S+) (0x[0-9A-F]+)', ins)
        rd, imm = rnum(m.group(1)), lit(m.group(2))
        vj += 1
        newV = f"V{vj}"
        w(f"  obtain ⟨n{k}, d{k}, I{k}', e{k}⟩ := pa_luiK env I{k-1} (by decide) pa_at_{o:x} (off' := {h(nxt)}) (by decide) (by decide)")
        w(f"  obtain ⟨{newV}, h{newV}⟩ : ∃ V, upd {vname} {rname(rd)} {h(imm)} = V := ⟨_, rfl⟩")
        w(f"  rw [h{newV}] at I{k}'")
        w(f"  have I{k} := I{k}'")
        nk = {}
        for r, (sym, p) in kvp.items():
            if r == rd:
                continue
            nk[r] = (sym, f"(by rw [← h{newV}, upd_ne (by decide) (by decide)]; exact {p})")
        nk[rd] = (('imm', imm), f"(by rw [← h{newV}, upd_same (by decide)])")
        vname = newV
        kvp = nk
        for r in list(kvp):
            sym, p = kvp[r]
            w(f"  have vk{k}_{r} : {vname} {rname(r)} = {vstr(sym)} := {p}")
            kvp[r] = (sym, f"vk{k}_{r}")
        assert not av
    else:
        raise Exception(ins)
    steps.append(f"d{k}")

assert ci == 46
assert W == 96 and set(outs) == {0, 0x20, 0x40}
inner = "de"
for s in reversed(steps):
    inner = f"({s}.trans {inner})"
w(f"  obtain ⟨mf, de, pcf, memf, spf, savf, keepf⟩ := pa_epi env I{k} (by decide) {kvp[2][1]}")
w(f"  have back : ∀ q, q.val ≠ 0 → q ≠ (8 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) →")
w(f"      q ≠ (21 : Fin 32) → {vname} q = V0 q := fun q h0 h8 h18 h19 h21 => by")
# V chain: each V_i = upd V_{i-1} rd _
vupd = re.findall(r'obtain ⟨(V\d+), hV\d+⟩ : ∃ V, upd (V\d+) (\(\d+ : Fin 32\)|\S+) ', "\n".join(L))
hyps = {'(8 : Fin 32)': 'h8', '(18 : Fin 32)': 'h18', '(19 : Fin 32)': 'h19', '(21 : Fin 32)': 'h21'}
seq = []
for newv, oldv, r in reversed(vupd):
    seq.append(f"← h{newv}, upd_ne h0 {hyps[r]}")
w(f"    rw [{', '.join(seq)}]")
w(f"  have hm : ∀ r c, (r, c) ∈ paPs → reg mf r = reg m r := fun r c h => (savf r c h).trans (psl r c h)")
w(f"  refine ⟨mf, c0.trans {inner}, ?_, spf, ?_, ?_, ?_⟩")
w(f"  · rw [pcf, psl ra 0x23C (by simp [paPs]), hra, hret]")
w(f"  · intro q q0 q1 q2 q3 q4 q5 q6 q7 qt0 qt1 qt2 qt3 qt4 qt5 qt6")
w(f"    by_cases h0 : q.val = 0")
w(f"    · have : q = 0 := Fin.ext h0")
w(f"      subst this; rfl")
w(f"    rcases pa_regs_cases q q0 q1 q2 q3 q4 q5 q6 q7 qt0 qt1 qt2 qt3 qt4 qt5 qt6 with")
w(f"      ⟨hk, hsp', h8, h9, h18, h19, h20, h21⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl")
w(f"    · rw [keepf q hk hsp' h8 h9 h18 h19 h20 h21, back q h0 h8 h18 h19 h21, ← hV0,")
w(f"        pk q hsp' (bkeep_ne hk (show paKeep a2 = false from rfl)) h9 h20]")
for r, c in (('ra', '0x23C'), ('(8 : Fin 32)', '0x238'), ('(9 : Fin 32)', '0x234'), ('(18 : Fin 32)', '0x230'),
             ('(19 : Fin 32)', '0x22C'), ('(20 : Fin 32)', '0x228'), ('(21 : Fin 32)', '0x224')):
    w(f"    · exact hm {r} {c} (by simp [paPs])")
w(f"    · rw [spf, hsp]")
w(f"  · rw [memf, hX1, hY1, hZ1, hX2, hY2, hZ2]")
w(f"    have ox := {outs[0][1]}")
w(f"    rw [add_ofNat_zero] at ox")
w(f"    rw [ox, show lhs + 0x20 = lhs + BitVec.ofNat 32 0x20 from rfl, {outs[0x20][1]},")
w(f"      show lhs + 0x40 = lhs + BitVec.ofNat 32 0x40 from rfl, {outs[0x40][1]}]")
w(f"    exact pa_spec_eq X1 Y1 Z1 X2 Y2 Z2 {' '.join(f'hv{i}' for i in range(1, vals + 1))}")
w(f"  · intro x hS hL")
w(f"    rw [memf]; exact I{k}.fr x hS hL")

hdr = '''import C3BootProofs.Proofs.PointEnv

/-!
# P-256 complete point addition, as compiled

Generated by `scripts/gen-point-add.py`; do not edit.
-/

namespace C3.RV32

open C3.Image

theorem pa_regs_cases : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 →
    q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) →
    q ≠ (31 : Fin 32) →
    (paKeep q = true ∧ q ≠ sp ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧
      q ≠ (20 : Fin 32) ∧ q ≠ (21 : Fin 32)) ∨
    q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
    q = (21 : Fin 32) ∨ q = sp := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The compiled P-256 point addition** (`primeorder`'s complete addition
for `a = -3`), called with `lhs` and `rhs` pointing at points in projective
coordinates, each coordinate below `p` in Montgomery form: it stores
`ptAddSpec` of them over `lhs`. It returns with `sp` and every register but
`a0` through `a7` and `t0` through `t6` as they were, and changes no memory
outside the 0x370 bytes of stack below `sp` and the 96 bytes at `lhs`. -/
theorem pointAdd_correct (m : Machine) {P sp0 lhs rhs retAddr : Word}
    (env : PAEnv m.mem P sp0 lhs rhs) (hpc : m.pc = P) (ha0 : reg m a0 = lhs) (ha1 : reg m a1 = rhs)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hx1 : limbVal (wordsAt m.mem lhs 8) < p256) (hy1 : limbVal (wordsAt m.mem (lhs + 0x20) 8) < p256)
    (hz1 : limbVal (wordsAt m.mem (lhs + 0x40) 8) < p256) (hx2 : limbVal (wordsAt m.mem rhs 8) < p256)
    (hy2 : limbVal (wordsAt m.mem (rhs + 0x20) 8) < p256) (hz2 : limbVal (wordsAt m.mem (rhs + 0x40) 8) < p256) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
        reg m' q = reg m q) ∧
      (limbVal (wordsAt m'.mem lhs 8), limbVal (wordsAt m'.mem (lhs + 0x20) 8),
        limbVal (wordsAt m'.mem (lhs + 0x40) 8)) =
        ptAddSpec bMont (limbVal (wordsAt m.mem lhs 8)) (limbVal (wordsAt m.mem (lhs + 0x20) 8))
          (limbVal (wordsAt m.mem (lhs + 0x40) 8)) (limbVal (wordsAt m.mem rhs 8))
          (limbVal (wordsAt m.mem (rhs + 0x20) 8)) (limbVal (wordsAt m.mem (rhs + 0x40) 8)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFC90) 0x370 x 1 → Sep lhs 96 x 1 → m'.mem x = m.mem x := by
'''
defs = re.findall(r'obtain ⟨(v\d+), (hv\d+)⟩ : ∃ v, (f[masd] \w+(?: \w+)?) = v', "\n".join(L))
specl = (f"/-- The values the generated proof names, chained, are `ptAddSpec`. -/\n"
         f"theorem pa_spec_eq (X1 Y1 Z1 X2 Y2 Z2 : Nat) {{{' '.join(v for v, _, _ in defs)} : Nat}}\n    "
         + "\n    ".join(f"({hv} : {e} = {v})" for v, hv, e in defs)
         + f" :\n    ({outs[0][0]}, {outs[0x20][0]}, {outs[0x40][0]}) = ptAddSpec bMont X1 Y1 Z1 X2 Y2 Z2 := by\n"
         f"  subst_vars; rfl\n\n")
hdr = hdr.replace("set_option maxHeartbeats 0 in\nset_option maxRecDepth", specl + "set_option maxHeartbeats 0 in\nset_option maxRecDepth")
out = hdr + "\n".join(L) + "\n\nend C3.RV32\n"
open(OUT, 'w').write(out)
