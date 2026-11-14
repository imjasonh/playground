#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/P384PtDouble.lean, the proof of the compiled
P-384 point doubling, from the decoded instructions in P384PtEnv.lean.

The body between the prologue's `memcpy` and the epilogue is argument setup
(`addi`, `mv`, `li`, `lui`) and 35 calls. This script simulates the argument
registers symbolically to find each call's result slot and operands, then
emits one step or call lemma from P384PtEnv.lean per instruction, names each
call's result after its field operation, and carries every frame slot's
value across the calls while a later call still reads it.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', 'C3BootProofs', 'Proofs') + os.sep
OUT = sys.argv[1] if len(sys.argv) > 1 else ROOT + 'P384PtDouble.lean'

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


src = open(ROOT + 'P384PtEnv.lean').read()
PD = decode(src, 'p3pd', 'p384PtDoubleCode')
offs = sorted(PD)
G = "d3G sp0"
CALLEES = {0x11C82: 'mul', 0x12426: 'sqr', 0x53A: 'add', 0x650: 'sub', 0x1235E: 'dbl', 0x12C54: 'cpy'}
OPF = {'mul': 'p3fm', 'sqr': 'p3fm', 'add': 'p3fa', 'sub': 'p3fs', 'dbl': 'p3fd'}
KEPT = {2, 8, 9, 18, 19, 20, 21, 22}
BADDR = 0x3FCC4234


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
    if t == 'sf':
        return "sf" if v[1] == 0 else f"sf + BitVec.ofNat 32 {h(v[1])}"
    if t == 'out':
        return "out"
    if t == 'b':
        return "p3bA"
    if t == 'imm':
        return h(v[1])
    raise Exception(v)


def pdst(c):
    assert 0x10 <= c and c + 48 <= 0x430 and c % 4 == 0, c
    return "⟨by decide, by decide, by decide⟩"


def body():
    for o in offs:
        if 0x36 <= o < 0x228:
            yield o


# ---------- pass 1: symbolic simulation, collect calls ----------
def simulate():
    kv = {2: ('G',), 9: ('sf', 0), 20: ('out',)}
    av = {}
    calls = []
    skip = set()
    for o in body():
        if o in skip:
            continue
        ins, ln = PD[o]
        kd = ins.split()[0]
        if kd == '.auipc':
            imm = lit(ins.split()[2])
            jins, _ = PD[o + 4]
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
                if base[0] == 'sf':
                    val = ('sf', base[1] + imm)
                elif base[0] == 'imm':
                    val = ('imm', (base[1] + imm) % 2 ** 32)
                    if val[1] == BADDR:
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
assert len(CALLS) == 35, len(CALLS)


def reads(c):
    o, kind, a0, a1, a2 = c
    srcs = [a1] if kind in ('dbl', 'sqr', 'cpy') else [a1, a2]
    return [s[1] for s in srcs if s[0] == 'slot']


SLOTS = range(0x10, 0x430, 4)
LIVE = []  # slots live after call j
for j in range(len(CALLS)):
    live = set()
    for c in SLOTS:
        for c2 in CALLS[j + 1:]:
            if c in reads(c2):
                live.add(c)
                break
            if c2[2] == ('slot', c):
                break
        else:
            if c in (0x10, 0x40, 0x70):
                live.add(c)
    LIVE.append(live)

# ---------- pass 2: emit ----------
L = []
w = L.append
INPUTS = {('sf', 0): 'X', ('sf', 0x30): 'Y', ('sf', 0x60): 'Z'}


def dsrc(v):
    if v[0] == 'slot':
        return f"(d3src_slot env {pdst(v[1])})"
    if v[0] == 'b':
        return "(d3src_b env)"
    return f"pS{v[1]:X}"


k = 0
vname = 'V0'
vj = 0
kvp = {}
av = {}
slots = {}
steps = []
vals = 0


def kreg(r):
    return f"((I{k}.keep {rname(r)} rfl).trans {kvp[r][1]})"


def regsym(r):
    return kvp[r][0] if r in KEPT else av[r][0]


def regp(r):
    if r in KEPT:
        return kreg(r)
    return av[r][1]


def sep_in(v):
    if v[1] == 0:
        return "(sep_base0 (env.sF.sub (c := 0) (l := 48) (by decide)))"
    return f"(env.sF.sub (c := {h(v[1])}) (l := 48) (by decide))"


def operand(v):
    """(value-name, proof of limbVal (wordsAt M_k a 12) = name, lt-proof)"""
    if v[0] == 'slot':
        return slots[v[1]]
    if v[0] == 'b':
        return ('p3B', f"((congrArg limbVal (I{k-1}.inp env.sK.symm)).trans (p3B_val env.bconst))", 'p3B_lt')
    nm = INPUTS[v]
    return (nm, f"((congrArg limbVal (I{k-1}.inp {sep_in(v)})).trans h{nm})", f"l{nm}")


w("  obtain ⟨n0, Ms, c0, I0, psp, ps1, ps4, pk, psl, pcp⟩ := d3_pro m env hpc ha0 ha1 hsp")
w("  obtain ⟨V0, hV0⟩ : ∃ V, reg n0 = V := ⟨_, rfl⟩")
w("  rw [hV0] at I0")
w("  have vsp0 : V0 sp = d3G sp0 := by rw [← hV0]; exact psp")
w("  have vs1_0 : V0 (9 : Fin 32) = sf := by rw [← hV0]; exact ps1")
w("  have vs4_0 : V0 (20 : Fin 32) = out := by rw [← hV0]; exact ps4")
kvp = {2: (('G',), 'vsp0'), 9: (('sf', 0), 'vs1_0'), 20: (('out',), 'vs4_0')}
for (side, off), nm in INPUTS.items():
    addr = "sf" if off == 0 else f"sf + {h(off)}"
    w(f"  obtain ⟨{nm}, h{nm}⟩ : ∃ v, limbVal (wordsAt m.mem ({addr}) 12) = v := ⟨_, rfl⟩")
    w(f"  have l{nm} : {nm} < p384 := by rw [← h{nm}]; exact h{nm.lower()}")
w("  have pS0 : D3Src sp0 sf := by")
w("    have := d3src_sf env 0 (by decide) (by decide); rwa [add_ofNat_zero] at this")
for off in (0x30, 0x60):
    w(f"  have pS{off:X} := d3src_sf env {h(off)} (by decide) (by decide)")
for c, nm, off in ((0x10, 'X', 0), (0x40, 'Y', 0x30), (0x70, 'Z', 0x60)):
    w(f"  have s0_{c:x} : limbVal (wordsAt Ms ({G} + BitVec.ofNat 32 {h(c)}) 12) = {nm} :=")
    ha = "(add_ofNat_zero sf).symm" if off == 0 else "rfl"
    w(f"    (congrArg limbVal (d3_copy_coord pcp {h(c)} {h(off)} {ha} rfl (by decide) (by decide))).trans h{nm}")
    slots[c] = (nm, f"s0_{c:x}", f"l{nm}")

ci = 0
skip = set()
for o in body():
    if o in skip:
        continue
    ins, ln = PD[o]
    kd = ins.split()[0]
    nxt = o + ln
    if kd == '.auipc':
        jo, kind, a0v, a1v, a2v = CALLS[ci]
        assert jo == o
        skip.add(o + 4)
        k += 1
        hb = "(by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)"
        assert a0v[0] == 'slot', (o, a0v)
        d = a0v[1]
        if kind == 'cpy':
            assert a1v[0] == 'slot' and a2v == ('imm', 0x30)
            s = a1v[1]
            w(f"  obtain ⟨n{k}, M{k}, d{k}, I{k}, f{k}, w{k}⟩ := d3_cpy (d := {h(d)}) (s := {h(s)}) env I{k-1}")
            w(f"    p3pd_at_{o:x} p3pd_at_{o+4:x} {hb} (by decide) {pdst(d)} {pdst(s)} (by decide)")
            w(f"    {av[10][1]}")
            w(f"    {av[11][1]}")
            w(f"    {av[12][1]}")
            sv_, sp_, sl = slots[s]
            newslots = {}
            for c in LIVE[ci]:
                if c == d:
                    continue
                nm, p, lt = slots[c]
                newslots[c] = (nm, f"((congrArg limbVal (d3slot_keep f{k} {pdst(d)} {pdst(c)} (by decide))).trans {p})", lt)
            if d in LIVE[ci]:
                newslots[d] = (sv_, f"((congrArg limbVal w{k}).trans {sp_})", sl)
            slots = newslots
        else:
            A = operand(a1v)
            line = (f"  obtain ⟨n{k}, M{k}, d{k}, I{k}, f{k}, w{k}⟩ := d3_{kind} (d := {h(d)}) env I{k-1} {kvp[2][1]}\n"
                    f"    p3pd_at_{o:x} p3pd_at_{o+4:x} {hb} (by decide) {pdst(d)}\n"
                    f"    {av[10][1]}\n"
                    f"    {dsrc(a1v)} {av[11][1]}")
            if kind in ('add', 'sub', 'mul'):
                B = operand(a2v)
                line += f"\n    {dsrc(a2v)} {av[12][1]}"
                if kind == 'mul':
                    line += f"\n    {A[1]} {B[1]} {B[2]}"
                else:
                    line += f"\n    {A[1]} {A[2]}\n    {B[1]} {B[2]}"
                expr = f"{OPF[kind]} {A[0]} {B[0]}"
            elif kind == 'sqr':
                line += f"\n    {A[1]} {A[2]}"
                expr = f"p3fm {A[0]} {A[0]}"
            else:
                line += f"\n    {A[1]} {A[2]}"
                expr = f"{OPF[kind]} {A[0]}"
            w(line)
            vals += 1
            v = f"v{vals}"
            w(f"  obtain ⟨{v}, h{v}⟩ : ∃ v, {expr} = v := ⟨_, rfl⟩")
            ltname = f"l{v}"
            fn = 'p3fm' if kind == 'sqr' else OPF[kind]
            args = ' _ _' if kind in ('mul', 'sqr', 'add', 'sub') else ' _'
            w(f"  have {ltname} : {v} < p384 := h{v} ▸ {fn}_lt{args}")
            newslots = {}
            for c in LIVE[ci]:
                if c == d:
                    continue
                nm, p, lt = slots[c]
                newslots[c] = (nm, f"((congrArg limbVal (d3slot_keep f{k} {pdst(d)} {pdst(c)} (by decide))).trans {p})", lt)
            if d in LIVE[ci]:
                newslots[d] = (v, f"(w{k}.trans h{v})", ltname)
            slots = newslots
        for c in list(slots):
            nm, p, lt = slots[c]
            w(f"  have s{k}_{c:x} : limbVal (wordsAt M{k} ({G} + BitVec.ofNat 32 {h(c)}) 12) = {nm} := {p}")
            slots[c] = (nm, f"s{k}_{c:x}", lt)
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
            w(f"  obtain ⟨n{k}, d{k}, I{k}', e{k}, o{k}⟩ := d3_addiK env I{k-1} p3pd_at_{o:x} (off' := {h(nxt)}) (by decide) (by decide)")
            k -= 1
            rsp = regp(rs)
            k += 1
            w(f"  obtain ⟨{newV}, h{newV}⟩ : ∃ V, upd {vname} {rname(rd)} (reg n{k-1} {rname(rs)} + {h(imm)}) = V := ⟨_, rfl⟩")
            w(f"  rw [h{newV}] at I{k}'")
            w(f"  have I{k} := I{k}'")
            if base[0] == 'G':
                val = ('slot', imm)
            elif base[0] == 'sf':
                val = ('sf', base[1] + imm)
            else:
                assert base[0] == 'imm'
                val = ('imm', (base[1] + imm) % 2 ** 32)
                if val[1] == BADDR:
                    val = ('b',)
            nk = {}
            for r, (sym, p) in kvp.items():
                if r == rd:
                    continue
                nk[r] = (sym, f"(by rw [← h{newV}, upd_ne (by decide) (by decide)]; exact {p})")
            nk[rd] = (val, f"(by rw [← h{newV}, upd_same (by decide), {rsp}] <;> rfl)")
            vname = newV
            kvp = nk
            for r in list(kvp):
                sym, p = kvp[r]
                w(f"  have vk{k}_{r} : {vname} {rname(r)} = {vstr(sym)} := {p}")
                kvp[r] = (sym, f"vk{k}_{r}")
            av = {r: (sym, f"((o{k} {rname(r)} (by decide)).trans {p})") for r, (sym, p) in av.items()}
        else:
            w(f"  obtain ⟨n{k}, d{k}, I{k}, e{k}, o{k}⟩ := d3_addi env I{k-1} p3pd_at_{o:x} (off' := {h(nxt)}) (by decide) rfl")
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
        w(f"  obtain ⟨n{k}, d{k}, I{k}, e{k}, o{k}⟩ := d3_mv env I{k-1} p3pd_at_{o:x} (off' := {h(nxt)}) (by decide) rfl")
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
        w(f"  obtain ⟨n{k}, d{k}, I{k}', e{k}⟩ := d3_luiK env I{k-1} p3pd_at_{o:x} (off' := {h(nxt)}) (by decide) (by decide)")
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

assert ci == 35
assert set(slots) == {0x10, 0x40, 0x70}, sorted(slots)
inner = "de"
for s in reversed(steps):
    inner = f"({s}.trans {inner})"
w(f"  obtain ⟨mf, de, pcf, memf, spf, savf, keepf⟩ := d3_epi env I{k} {kvp[2][1]} {kvp[20][1]}")
vupd = re.findall(r'obtain ⟨(V\d+), hV\d+⟩ : ∃ V, upd (V\d+) (\(\d+ : Fin 32\)|\S+) ', "\n".join(L))
kept = sorted({r for _, _, r in vupd})
hyps = {r: "h" + re.match(r"\((\d+)", r).group(1) for r in kept}
w(f"  have back : ∀ q, q.val ≠ 0 → {' → '.join(f'q ≠ {r}' for r in kept)} → {vname} q = V0 q :=")
w(f"    fun q h0 {' '.join(hyps[r] for r in kept)} => by")
seq = []
for newv, oldv, r in reversed(vupd):
    seq.append(f"← h{newv}, upd_ne h0 {hyps[r]}")
w(f"    rw [{', '.join(seq)}]")
w(f"  have hm : ∀ r c, (r, c) ∈ d3Ps → reg mf r = reg m r := fun r c h => (savf r c h).trans (psl r c h)")
w(f"  refine ⟨mf, c0.trans {inner}, ?_, spf, ?_, ?_, ?_⟩")
w(f"  · rw [pcf, psl ra 0x44C (by simp [d3Ps]), hra, hret]")
w(f"  · intro q q0 q1 q2 q3 q4 q5 q6 q7 qt0 qt1 qt2 qt3 qt4 qt5 qt6")
w(f"    by_cases h0 : q.val = 0")
w(f"    · have : q = 0 := Fin.ext h0")
w(f"      subst this; rfl")
w(f"    rcases d3_regs_cases q q0 q1 q2 q3 q4 q5 q6 q7 qt0 qt1 qt2 qt3 qt4 qt5 qt6 with")
w(f"      ⟨hk, hsp', h8, h9, h18, h19, h20, h21, h22⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl")
w(f"    · rw [keepf q hk (d3_notin h0 hsp' h8 h9 h18 h19 h20 h21 h22),")
w(f"        back q h0 {' '.join(hyps[r] for r in kept)}, ← hV0, pk q hk hsp' h9 h20]")
for r, c in (('ra', '0x44C'), ('(8 : Fin 32)', '0x448'), ('(9 : Fin 32)', '0x444'), ('(18 : Fin 32)', '0x440'),
             ('(19 : Fin 32)', '0x43C'), ('(20 : Fin 32)', '0x438'), ('(21 : Fin 32)', '0x434'),
             ('(22 : Fin 32)', '0x430')):
    w(f"    · exact hm {r} {c} (by simp [d3Ps])")
w(f"    · rw [spf, hsp]")
w(f"  · rw [memf, hX, hY, hZ]")
w(f"    rw [d3_out_coord (a := out) 0 0x10 (add_ofNat_zero out).symm rfl (by decide) (by decide) env.hwo,")
w(f"      d3_out_coord (a := out + 0x30) 0x30 0x40 rfl rfl (by decide) (by decide) env.hwo,")
w(f"      d3_out_coord (a := out + 0x60) 0x60 0x70 rfl rfl (by decide) (by decide) env.hwo]")
w(f"    rw [{slots[0x10][1]}, {slots[0x40][1]}, {slots[0x70][1]}]")
w(f"    exact d3_spec_eq X Y Z {' '.join(f'hv{i}' for i in range(1, vals + 1))}")
w(f"  · intro x hS hO")
w(f"    rw [memf, copyWords_outside 36 hO]; exact I{k}.fr x hS")

defs = re.findall(r'obtain ⟨(v\d+), (hv\d+)⟩ : ∃ v, (p3f[masd] \w+(?: \w+)?) = v', "\n".join(L))
specl = (f"/-- The values the generated proof names, chained, are `p3Dbl`. -/\n"
         f"theorem d3_spec_eq (X Y Z : Nat) {{{' '.join(v for v, _, _ in defs)} : Nat}}\n    "
         + "\n    ".join(f"({hv} : {e} = {v})" for v, hv, e in defs)
         + f" :\n    ({slots[0x10][0]}, {slots[0x40][0]}, {slots[0x70][0]}) = p3Dbl p3B X Y Z := by\n"
         f"  subst_vars; rfl\n\n")

hdr = '''import C3BootProofs.Proofs.P384PtEnv

/-!
# P-384 point doubling, as compiled

Generated by `scripts/gen-p384-double.py`; do not edit.
-/

namespace C3.RV32

open C3.Image

set_option synthInstance.maxSize 4096 in
theorem d3_regs_cases : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 →
    q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) →
    q ≠ (31 : Fin 32) →
    (d3Keep q = true ∧ q ≠ sp ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧
      q ≠ (20 : Fin 32) ∧ q ≠ (21 : Fin 32) ∧ q ≠ (22 : Fin 32)) ∨
    q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
    q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = sp := by decide

theorem d3_notin {q : Fin 32} (h0 : q.val ≠ 0) (hsp : q ≠ sp) (h8 : q ≠ (8 : Fin 32)) (h9 : q ≠ (9 : Fin 32))
    (h18 : q ≠ (18 : Fin 32)) (h19 : q ≠ (19 : Fin 32)) (h20 : q ≠ (20 : Fin 32)) (h21 : q ≠ (21 : Fin 32))
    (h22 : q ≠ (22 : Fin 32)) : q.val ∉ [0, 2, 8, 9, 18, 19, 20, 21, 22] := by
  intro h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h
  · exact h0 h
  · exact hsp (Fin.ext h)
  · exact h8 (Fin.ext h)
  · exact h9 (Fin.ext h)
  · exact h18 (Fin.ext h)
  · exact h19 (Fin.ext h)
  · exact h20 (Fin.ext h)
  · exact h21 (Fin.ext h)
  · exact h22 (Fin.ext h)

SPEC
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **The compiled P-384 point doubling** (`primeorder`'s doubling for
`a = -3`), called with `sf` pointing at a point in projective coordinates,
each coordinate below `p` in Montgomery form, and the result at `out`: it
stores `p3Dbl` of the point at `out`. It returns with `sp` and every register
but `a0` through `a7` and `t0` through `t6` as they were, and changes no
memory outside the 0x540 bytes of stack below `sp` and the 144 bytes at
`out`. -/
theorem p384PtDouble_correct (m : Machine) {P sp0 out sf retAddr : Word}
    (env : D3Env m.mem P sp0 out sf) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = sf)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hx : limbVal (wordsAt m.mem sf 12) < p384) (hy : limbVal (wordsAt m.mem (sf + 0x30) 12) < p384)
    (hz : limbVal (wordsAt m.mem (sf + 0x60) 12) < p384) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
        reg m' q = reg m q) ∧
      (limbVal (wordsAt m'.mem out 12), limbVal (wordsAt m'.mem (out + 0x30) 12),
        limbVal (wordsAt m'.mem (out + 0x60) 12)) =
        p3Dbl p3B (limbVal (wordsAt m.mem sf 12)) (limbVal (wordsAt m.mem (sf + 0x30) 12))
          (limbVal (wordsAt m.mem (sf + 0x60) 12)) ∧
      ∀ x, Sep (d3S sp0) 0x540 x 1 → Sep out 144 x 1 → m'.mem x = m.mem x := by
'''
hdr = hdr.replace("SPEC\n", specl)
out = hdr + "\n".join(L) + "\n\nend C3.RV32\n"
open(OUT, 'w').write(out)
