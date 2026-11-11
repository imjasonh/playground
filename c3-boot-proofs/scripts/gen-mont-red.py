#!/usr/bin/env python3
"""Writes C3BootProofs/Proofs/FieldMontRed.lean, the proof of the Montgomery
reduction block in FieldElement::multiply.

It runs the decoded block (FieldDecode.lean's fm_at lemmas) and p256's
montgomery_reduce side by side on inputs that make the carries fire, matches
each compiled value to a value of the Rust code, sorts each carrying_add and
carrying_mul_add into the instruction idiom that fmP1, fmP3, or fmP4 covers,
and writes one step per instruction, one carry equation per Rust operation,
and the round sums. Run it from c3-boot-proofs/ after FieldDecode.lean
changes; CI checks that the committed file matches.
"""
import os, random, re

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
random.seed(710)

M32 = (1<<32)-1
src = open(os.path.join(ROOT, 'C3BootProofs/Proofs/FieldDecode.lean')).read()
ins = []
for m in re.finditer(r'theorem fm_at_(\w+) : fetchRel fieldMulCode (0x[0-9A-Fa-f]+) = some \((.*), (\d)\) := by decide', src):
    off = int(m.group(2),16); ins.append((off, m.group(3)))
ins.sort()
names = {'ra':1,'sp':2,'x0':0,'t0':5,'a0':10,'a1':11,'a2':12,'a3':13,'a4':14,'a5':15,'a6':16,'a7':17}
def reg(s):
    s=s.strip()
    m=re.match(r'\((\d+) : Fin 32\)',s)
    if m: return int(m.group(1))
    return names[s]
def toks(s):
    # split top-level by spaces respecting parens
    out=[];depth=0;cur=''
    for ch in s:
        if ch=='(' : depth+=1
        if ch==')' : depth-=1
        if ch==' ' and depth==0:
            if cur: out.append(cur); cur=''
        else: cur+=ch
    if cur: out.append(cur)
    return out
block = [(o,i) for (o,i) in ins if 0x20 <= o < 0x28C]
def run(T):
    R=[random.getrandbits(32) for _ in range(32)]; R[0]=0; R[2]=0x1000
    mem={0x1000+4*k:T[k] for k in range(16)}
    trace=[]
    for off,i in block:
        t=toks(i[1:] if i.startswith('.') else i)
        op=t[0]
        if op=='.load' or op=='load':
            rd=reg(t[2]); rs=reg(t[3]); imm=int(t[4],16); v=mem[(R[rs]+imm)&M32]
        elif op in('.alu','alu'):
            f=t[1].lstrip('.'); rd=reg(t[2]); a=R[reg(t[3])]; b=R[reg(t[4])]
            v={'add':(a+b)&M32,'sub':(a-b)&M32,'sltu':int(a<b),'mulhu':(a*b)>>32,'mul':(a*b)&M32}[f]
        elif op in('.aluImm','aluImm'):
            f=t[1].lstrip('.'); rd=reg(t[2]); a=R[reg(t[3])]; imm=int(t[4],16)
            v={'add':(a+imm)&M32}[f]
        else: raise Exception(i)
        if rd: R[rd]=v
        trace.append((off,i,rd,v))
    return trace,R
def ca(a,b,c):
    s=a+b+c; return s&M32, s>>32
def cma(a,b,c,d):
    s=a*b+c+d; return s&M32, s>>32
def source(T):
    a=list(T); V={}
    def rec(n,v): V[n]=v
    M7=M32
    a3,c=ca(a[3],0,a[0]); rec('r0a3',a3); rec('r0c1',c)
    a4,c=ca(a[4],0,c); rec('r0a4',a4); rec('r0c2',c)
    a5,c=ca(a[5],0,c); rec('r0a5',a5); rec('r0c3',c)
    a6,c=ca(a[6],a[0],c); rec('r0a6',a6); rec('r0c4',c)
    a7,c=cma(a[0],M7,a[7],c); rec('r0a7',a7); rec('r0c5',c)
    a8,c2=ca(a[8],0,c); rec('r0a8',a8); rec('r0cc',c2)
    L=[a[0],a[1],a[2],a3,a4,a5,a6,a7,a8]+a[9:16]
    for i in range(1,8):
        m=L[i]
        x,c=ca(L[i+3],0,m); L[i+3]=x; rec(f'r{i}a{i+3}',x); rec(f'r{i}c1',c)
        x,c=ca(L[i+4],0,c); L[i+4]=x; rec(f'r{i}a{i+4}',x); rec(f'r{i}c2',c)
        x,c=ca(L[i+5],0,c); L[i+5]=x; rec(f'r{i}a{i+5}',x); rec(f'r{i}c3',c)
        x,c=ca(L[i+6],m,c); L[i+6]=x; rec(f'r{i}a{i+6}',x); rec(f'r{i}c4',c)
        x,c=cma(m,M7,L[i+7],c); L[i+7]=x; rec(f'r{i}a{i+7}',x); rec(f'r{i}c5',c)
        if i<7:
            x,c2=ca(L[i+8],c2,c); L[i+8]=x; rec(f'r{i}a{i+8}',x); rec(f'r{i}cc',c2)
        else:
            x,c16=ca(L[15],c2,c); L[15]=x; rec('r7a15',x); rec('a16',c16); L.append(c16)
    for k in range(16): V[f'T{k}']=T[k]
    return V, L[8:17]

# Static single assignment over the block.
def parse(i):
    t=toks(i)
    op=t[0].lstrip('.')
    if op=='load': return ('lw', reg(t[2]), reg(t[3]), int(t[4],16))
    if op=='alu': return (t[1].lstrip('.'), reg(t[2]), reg(t[3]), reg(t[4]))
    if op=='aluImm': return (t[1].lstrip('.')+'i', reg(t[2]), reg(t[3]), int(t[4],16))
    raise Exception(i)
P=[]  # list of dict
cur={}
for off,i in block:
    op,rd,a,b=parse(i)
    if op=='lw': args=[['reg',a] if a not in cur else ['v',cur[a]]]
    elif op.endswith('i'): args=[['reg',a] if a not in cur else ['v',cur[a]], ['imm',b]]
    else: args=[(['reg',x] if x not in cur else ['v',cur[x]]) if x!=0 else ['zero',0] for x in (a,b)]
    P.append(dict(off=off,op=op,rd=rd,args=args,imm=b if op in('lw',) else None))
    cur[rd]=len(P)-1
# values
trials=[]
for t in range(1500):
    T=[random.choice([0,M32,M32,M32,1,M32-1,random.getrandbits(32),random.getrandbits(32)]) for _ in range(16)]
    tr,R=run(T); V,L=source(T); trials.append((tr,V))
name={}
for idx in range(len(P)):
    c=[n for n in trials[0][1] if all(tr[idx][3]==V[n] for (tr,V) in trials)]
    if c: name[idx]=c[0]

# Each Rust operation's instruction group.
byname={}
for k,v in name.items(): byname.setdefault(v,[]).append(k)
def prod(n):
    ks=byname[n]; return max(ks)  # last producer (final value)
def arg(i,j):
    a=P[i]['args'][j]; return a[1] if a[0]=='v' else ('ZERO' if a[0]=='zero' or a==['reg',0] else a)
def nm(v): return name.get(v, '?%s'%hex(P[v]['off'])) if isinstance(v,int) else str(v)
def P1(y,c,xa,xb):
    iy=prod(y); ic=[k for k in byname[c] if P[k]['op']=='sltu' and arg(k,0)==iy]; assert len(ic)==1,(y,c); ic=ic[0]
    assert P[iy]['op']=='add' and P[ic]['op']=='sltu', (y,c)
    assert arg(ic,0)==iy
    cmp=arg(ic,1)
    return dict(kind='P1',y=iy,c=ic,a=arg(iy,0),b=arg(iy,1),cmp=cmp)
def P3(y,c):
    iy,ic=prod(y),prod(c)
    assert P[iy]['op']=='add' and P[ic]['op']=='add'
    # y = add(u,v): one of u,v is t=add(a,b); other is carry-in
    a0,a1=arg(iy,0),arg(iy,1)
    def isadd(v): return isinstance(v,int) and P[v]['op']=='add'
    # carry = add(p,q) where p,q are sltu's
    p,q=arg(ic,0),arg(ic,1)
    assert P[p]['op']=='sltu' and P[q]['op']=='sltu'
    # find which sltu is sltu(y, t)
    if arg(p,0)==iy: c2,c1=p,q
    else: c2,c1=q,p
    assert arg(c2,0)==iy
    t=arg(c2,1)
    assert P[t]['op']=='add'
    cin = a1 if a0==t else a0
    assert t in (a0,a1)
    assert arg(c1,0)==t
    return dict(kind='P3',y=iy,c=ic,t=t,cin=cin,ta=arg(t,0),tb=arg(t,1),c1=c1,c1cmp=arg(c1,1),c2=c2,yorder='t_first' if a0==t else 'cin_first',corder='c2_first' if p==c2 else 'c1_first')
def P4(y,c):
    iy,ic=prod(y),prod(c)
    a0,a1=arg(iy,0),arg(iy,1)
    d = a0 if P[a0]['op']=='sub' else a1
    cin = a1 if d==a0 else a0
    assert P[d]['op']=='sub'
    x,m=arg(d,0),arg(d,1)
    # collect leaves of carry add-tree
    leaves=[]
    def walk(v):
        if P[v]['op']=='add' and v!=d: walk(arg(v,0)); walk(arg(v,1))
        else: leaves.append(v)
    walk(ic)
    desc=[]
    for l in leaves:
        o=P[l]['op']
        if o=='mulhu': desc.append(('mulhu',nm(arg(l,0))))
        elif o=='sltu': desc.append(('sltu',nm(arg(l,0)),nm(arg(l,1))))
        else: desc.append((o,))
    return dict(kind='P4',y=iy,c=ic,d=d,x=x,m=m,cin=cin,yorder='d_first' if a0==d else 'cin_first',leaves=desc,tree=str(tree(ic,d)))
def tree(v,d):
    if P[v]['op']=='add': return (tree(arg(v,0),d),tree(arg(v,1),d))
    o=P[v]['op']
    if o=='sltu':
        a,b=arg(v,0),arg(v,1)
        if a==d: return 'S(d,%s)'%('x' if b==P[d]['args'][0][1] else ('neg' if P[b]['op']=='sub' else nm(b)))
        return 'S(r,d)' if b==d else 'S(%s,%s)'%(nm(a),nm(b))
    if o=='mulhu': return 'H'
    return o
recs=[]
for i in range(8):
    recs.append((i,'r3',P1(f'r{i}a{i+3}',f'r{i}c1',None,None)))
    recs.append((i,'r4',P1(f'r{i}a{i+4}',f'r{i}c2',None,None)))
    recs.append((i,'r5',P1(f'r{i}a{i+5}',f'r{i}c3',None,None)))
    recs.append((i,'r6',P3(f'r{i}a{i+6}',f'r{i}c4')))
    recs.append((i,'r7',P4(f'r{i}a{i+7}',f'r{i}c5')))
    if i==0: recs.append((i,'r8',P1('r0a8','r0cc',None,None)))
    elif i<7: recs.append((i,'r8',P3(f'r{i}a{i+8}',f'r{i}cc')))
    else: recs.append((i,'r8',P3('r7a15','a16')))

# The round identities and their sum.
byname={}
for k,v in name.items(): byname.setdefault(v,[]).append(k)
def arg(i,j):
    a=P[i]['args'][j]; return a[1] if a[0]=='v' else None
def ssa(n): return byname[n][0]
mname=['T0','T1','T2','r0a3','r1a4','r2a5','r3a6','r4a7']
Ms=[ssa(x) for x in mname]
# limb tracking
cur={k:ssa(f'T{k}') for k in range(16)}
rounds=[]
cc=None
for i in range(8):
    R={kk:rr for (ii,kk,rr) in recs if ii==i}
    m=Ms[i]
    xs=[cur[i+3+j] for j in range(6)]
    ys=[R['r3']['y'],R['r4']['y'],R['r5']['y'],R['r6']['y'],R['r7']['y'],R['r8']['y']]
    co=R['r8']['c']
    rounds.append((xs,m,cc,ys,co))
    for j in range(6): cur[i+3+j]=ys[j]
    cc=co
outs=[cur[k] for k in range(8,16)]+[cc]
T=[ssa(f'T{k}') for k in range(16)]
v=lambda k:f'v{k}'
def rtype(xs,m,ci,ys,co):
    x3,x4,x5,x6,x7,x8=map(v,xs); y3,y4,y5,y6,y7,y8=map(v,ys)
    ci_ = v(ci) if ci is not None else '0'
    return (f"{y3} + 2 ^ 32 * {y4} + 2 ^ 64 * {y5} + 2 ^ 96 * {y6} + 2 ^ 128 * {y7} + 2 ^ 160 * {y8} + 2 ^ 192 * {v(co)} + 2 ^ 128 * {v(m)} = "
            f"{x3} + 2 ^ 32 * {x4} + 2 ^ 64 * {x5} + 2 ^ 96 * {x6} + 2 ^ 128 * {x7} + 2 ^ 160 * {x8} + 2 ^ 160 * {ci_} + {v(m)} * (1 + 2 ^ 96 + 2 ^ 160)")
allv=sorted({x for r in rounds for x in r[0]+r[3]+[r[1],r[4]]+([r[2]] if r[2] is not None else [])}|set(T)|set(outs))
L=sum_=lambda ws:" + ".join(f"2 ^ {32*j} * {v(w)}" for j,w in enumerate(ws))
P256=2**256 - 2**224 + 2**192 + 2**96 - 1
mq=" + ".join(f"2 ^ {32*i} * {v(Ms[i])}" for i in range(8))

# standalone lemmas for the real file
Wv=" ".join(v(x) for x in allv)
lt=[]
def flat(nn):
    vs=" ".join(f"a{j}" for j in range(nn))
    body=" + ".join(f"2 ^ {32*j} * a{j}.toNat" for j in range(nn))
    return [f"theorem limbFlat{nn} ({vs} : Word) :",
            f"    limbVal [{', '.join(f'a{j}' for j in range(nn))}] =",
            f"      {body} := by",
            "  simp only [limbVal, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_zero, Nat.add_zero]",
            "  omega", ""]
lt+=flat(9)+flat(16)
lt.append("set_option maxHeartbeats 4000000 in")
lt.append("/-- The eight rounds summed: the reduction's output words times `2^256` are")
lt.append("the product plus `q · p`. -/")
lt.append(f"theorem mont_tele ({Wv} : Word)")
for i,r in enumerate(rounds):
    t=rtype(*r)
    import re as _re
    t=_re.sub(r'\bv(\d+)\b', lambda mm: f'v{mm.group(1)}.toNat', t)
    lt.append(f"    (R{i} : {t})")
lt.append(f"    : limbVal [{', '.join(v(x) for x in outs)}] * 2 ^ 256 =")
lt.append(f"      limbVal [{', '.join(v(x) for x in T)}] +")
lt.append(f"        ({' + '.join(f'2 ^ {32*i} * {v(Ms[i])}.toNat' for i in range(8))}) * p256 := by")
lt.append(f"  rw [limbFlat9, limbFlat16, show p256 = {P256} from rfl]")
lt.append("  omega")
lt.append("")
lt.append("theorem mq_bound (a0 a1 a2 a3 a4 a5 a6 a7 : Word) :")
lt.append("    2 ^ 0 * a0.toNat + 2 ^ 32 * a1.toNat + 2 ^ 64 * a2.toNat + 2 ^ 96 * a3.toNat + 2 ^ 128 * a4.toNat +")
lt.append("      2 ^ 160 * a5.toNat + 2 ^ 192 * a6.toNat + 2 ^ 224 * a7.toNat < 2 ^ 256 := by")
lt.append("  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt")
lt.append("  have := a4.isLt; have := a5.isLt; have := a6.isLt; have := a7.isLt")
lt.append("  omega")
TELE="\n".join(lt)+"\n"
TELEV=dict(allv=allv,outs=outs,T=T,Ms=Ms)

# The proof.
byname={}
for k,v in name.items(): byname.setdefault(v,[]).append(k)
REGN={1:'ra',2:'sp',10:'a0',11:'a1',12:'a2',13:'a3',14:'a4',15:'a5',16:'a6',17:'a7'}
def rn(r): return REGN.get(r, f'({r} : Fin 32)')
def arg(i,j):
    a=P[i]['args'][j]; return a[1] if a[0]=='v' else None
V=lambda k: f'v{k}'
HV=lambda k: f'hv{k}'
N=len(P)
offs=[p['off'] for p in P]
nexto=offs[1:]+[0x28C]
L=[]
w=L.append
w('set_option maxHeartbeats 40000000 in')
w('set_option maxRecDepth 100000 in')
w('/-- **The compiled Montgomery reduction**, the straight-line block from 0x20 to 0x28C')
w('of `FieldElement::multiply`: from the 16-word product at `G`, the nine words it')
w('leaves for `sub_inner` times `2^256` are the product plus `q · p` for some')
w('`q < 2^256`. -/')
w('theorem fm_red {M : Word → BitVec 8} {B G : Word} {n : Machine} (s : St M B n 0x20 (reg n))')
w('    (hc : CodeIn M B fieldMulCode) (hsp : reg n sp = G) (hG : G.toNat % 4 = 0) :')
w('    ∃ n\', Steps n n\' ∧ St M B n\' 0x28C (reg n\') ∧')
w('      (∃ q, q < 2 ^ 256 ∧ limbVal [reg n\' (7 : Fin 32), reg n\' (6 : Fin 32), reg n\' (5 : Fin 32), reg n\' a5,')
w('        reg n\' a4, reg n\' a0, reg n\' a1, reg n\' a2, reg n\' a3] * 2 ^ 256 = limbVal (wordsAt M G 16) + q * p256) ∧')
w('      reg n\' (19 : Fin 32) = 0xFFFFFFFF ∧ ∀ q, fmRedKeep q = true → reg n\' q = reg n q := by')
prev='s'
for k,p in enumerate(P):
    off=p['off']; nx=nexto[k]
    if p['op']=='lw':
        alg = f"(by rw [hsp]; exact aligned_add hG (k := {p['imm']}) (by decide))" if k==0 else f"(by simp +decide only [upd, ↓reduceIte, hsp]; exact aligned_add hG (k := {p['imm']}) (by decide))"
        w(f"  obtain ⟨n{k}, {V(k)}, d{k}, {HV(k)}, u{k}⟩ := {prev}.lwG hc fm_at_{off:x} (off' := 0x{nx:X}) (by decide)")
        w(f"    {alg}")
        if k==0: w(f"  rw [hsp] at {HV(k)}")
        else: w(f"  simp +decide only [upd, ↓reduceIte, hsp] at {HV(k)}")
    elif p['op'].endswith('i'):
        w(f"  obtain ⟨n{k}, {V(k)}, d{k}, {HV(k)}, u{k}⟩ := {prev}.aluImmG hc fm_at_{off:x} (off' := 0x{nx:X}) (by decide)")
        w(f"  simp +decide only [upd, ↓reduceIte] at {HV(k)}")
    else:
        w(f"  obtain ⟨n{k}, {V(k)}, d{k}, {HV(k)}, u{k}⟩ := {prev}.aluG hc fm_at_{off:x} (off' := 0x{nx:X}) (by decide)")
        w(f"  simp +decide only [upd, ↓reduceIte] at {HV(k)}")
    prev=f'u{k}'
last=N-1
# final register producers
cur={}
for k,p in enumerate(P): cur[p['rd']]=k
written=sorted(cur.keys())
outs=[7,6,5,15,14,10,11,12,13]
for r in outs+[19]:
    w(f"  have o{r} : reg n{last} {rn(r)} = {V(cur[r])} := by rw [u{last}.regs]; simp +decide only [upd, ↓reduceIte]")
# s3
s3=cur[19]
w(f"  have s3e : {V(s3)} = 0xFFFFFFFF := by rw [← {HV(s3)}]; rfl")
for k,p in enumerate(P):
    if p['op']=='mulhu': w(f"  rw [s3e] at {HV(k)}")
# E's
def ssa_of(nm_):
    ks=byname[nm_]; assert len(ks)==1, nm_; return ks[0]
mname=['T0','T1','T2','r0a3','r1a4','r2a5','r3a6','r4a7']
Ms=[ssa_of(x) for x in mname]
R=[]
for (i,kind,r) in recs:
    m=Ms[i]
    E=f'E{i}_{kind}'
    if r['kind']=='P1':
        a,b,y,c,cmp=r['a'],r['b'],r['y'],r['c'],r['cmp']
        if kind=='r3': first = b if a==m else a   # x3
        elif kind in('r4','r5'):
            prevc = {'r4':'r3','r5':'r4'}[kind]
            pc=[rr for (ii,kk,rr) in recs if ii==i and kk==prevc][0]['c']
            first = b if a==pc else a
        else:  # round 0 r8: x8 + c5
            c5=[rr for (ii,kk,rr) in recs if ii==i and kk=='r7'][0]['c']
            first = b if a==c5 else a
        lem='fmP1' if a==first else 'fmP1s'
        hc_='.inl' if cmp==a else '.inr'
        if kind=='r8':
            w(f"  have {E} : {V(y)}.toNat + 2 ^ 32 * {V(c)}.toNat = {V(first)}.toNat + 0 + {V(b if first==a else a)}.toNat := by")
            w(f"    rw [Nat.add_zero]; exact {lem} {HV(y)} ({hc_} {HV(c)})")
        else:
            w(f"  have {E} := {lem} {HV(y)} ({hc_} {HV(c)})")
    elif r['kind']=='P3':
        t=r['t']; ta,tb=r['ta'],r['tb']; y=r['y']; c=r['c']; c1=r['c1']; c2=r['c2']; cin=r['cin']
        if kind=='r6': x=[v for v in (ta,tb) if v!=m]; x=x[0] if x else ta
        else:
            # r8: (x8, cc_prev)
            cc=[rr for (ii,kk,rr) in recs if ii==i-1 and kk=='r8'][0]['c']
            x = ta if tb==cc else tb
        lem='fmP3' if ta==x else 'fmP3s'
        h1='.inl' if r['c1cmp']==ta else '.inr'
        hy='.inl' if r['yorder']=='cin_first' else '.inr'
        hcc='.inl' if r['corder']=='c2_first' else '.inr'
        w(f"  have {E} := {lem} {HV(t)} ({h1} {HV(c1)}) ({hy} {HV(y)}) {HV(c2)} ({hcc} {HV(c)})")
    else:
        d=r['d']; y=r['y']; c=r['c']
        # find leaves
        def leaves(v):
            if P[v]['op']=='add' and v!=d and v!=y: return leaves(arg(v,0))+leaves(arg(v,1))
            return [v]
        lv=leaves(c)
        h=[v for v in lv if P[v]['op']=='mulhu'][0]
        sr=[v for v in lv if P[v]['op']=='sltu' and arg(v,0)==y][0]
        sb=[v for v in lv if P[v]['op']=='sltu' and arg(v,0)==d][0]
        xx=arg(d,0)
        if arg(sb,1)==xx: hb=f'(.inl {HV(sb)})'
        else:
            neg=arg(sb,1); hb=f'(.inr (by rw [{HV(neg)}]; exact {HV(sb)}))'
        hy='.inl' if arg(y,0)==d else '.inr'
        # tree
        c0,c1_=arg(c,0),arg(c,1)
        if c0==sr:
            inner=c1_; shape = 1 if arg(inner,0)==sb else 2
        else:
            inner=c0; shape = 3 if arg(inner,0)==sb else 4
        pre={1:'.inl',2:'.inr (.inl',3:'.inr (.inr (.inl',4:'.inr (.inr (.inr'}[shape]
        close={1:'',2:')',3:'))',4:'))'}[shape]
        hcp=f'({pre} (by rw [← {HV(c)}, ← {HV(inner)}]){close})'
        w(f"  have {E} := fmP4 (sb := {V(sb)}) (c := {V(c)}) {HV(d)} {HV(h)} {hb} ({hy} {HV(y)}) {HV(sr)} {hcp}")
for i in range(8):
    w(f"  have R{i} := mont_round E{i}_r3 E{i}_r4 E{i}_r5 E{i}_r6 E{i}_r7 E{i}_r8")
w("  clear " + " ".join(f"E{i}_{k}" for i in range(8) for k in ['r3','r4','r5','r6','r7','r8']))
# loads in offset order
loads={P[k]['imm']:k for k in range(N) if P[k]['op']=='lw'}
order=[loads[4*j] for j in range(16)]
steps=" ".join(f"(.cons d{k}" for k in range(N-1))
w(f"  refine ⟨n{last}, {steps} (.single d{last}){')'*(N-1)}, u{last}.self, ?_, o19.trans s3e, ?_⟩")
mq=" + ".join(f"2 ^ {32*i} * {V(Ms[i])}.toNat" for i in range(8))
T=TELEV
w(f"  · refine ⟨{mq}, mq_bound {' '.join(V(k) for k in Ms)}, ?_⟩")
w(f"    rw [{', '.join('o%d'%r for r in outs)}, wordsAt16, {', '.join(HV(k) for k in order)}]")
w(f"    exact mont_tele {' '.join(V(k) for k in T['allv'])} R0 R1 R2 R3 R4 R5 R6 R7")
w(f"  · intro q hq")
w(f"    rw [u{last}.regs]")
ne=" ".join(f"(bkeep_ne hq (r := {rn(r)}) rfl)" for r in written)
w(f"    have ⟨{', '.join('q%d'%r for r in written)}⟩ : {' ∧ '.join('q ≠ '+rn(r) for r in written)} :=")
w(f"      ⟨{', '.join('bkeep_ne hq (r := %s) rfl'%rn(r) for r in written)}⟩")
w(f"    by_cases h0 : q.val = 0")
w(f"    · have : q = 0 := Fin.ext h0")
w(f"      subst this; simp [upd]; exact s.zero.symm")
w(f"    · simp [upd, h0, {', '.join('q%d'%r for r in written)}]")
hdr=f'''import C3BootProofs.Proofs.FieldMont

/-! # The Montgomery reduction in `FieldElement::multiply`, as compiled

`scripts/gen-mont-red.py` writes this file from the decoded instructions. -/

namespace C3.RV32

open C3.ImageV0

/-- The registers the reduction block leaves alone. -/
def fmRedKeep (q : Fin 32) : Bool := q.val ∉ {written}

theorem wordsAt16 (M : Word → BitVec 8) (b : Word) :
    wordsAt M b 16 = [memLoad32 M (b + 0x0), memLoad32 M (b + 0x4), memLoad32 M (b + 0x8), memLoad32 M (b + 0xC),
      memLoad32 M (b + 0x10), memLoad32 M (b + 0x14), memLoad32 M (b + 0x18), memLoad32 M (b + 0x1C),
      memLoad32 M (b + 0x20), memLoad32 M (b + 0x24), memLoad32 M (b + 0x28), memLoad32 M (b + 0x2C),
      memLoad32 M (b + 0x30), memLoad32 M (b + 0x34), memLoad32 M (b + 0x38), memLoad32 M (b + 0x3C)] := rfl

'''
hdr+=TELE+"\n"
open(os.path.join(ROOT, 'C3BootProofs/Proofs/FieldMontRed.lean'),'w').write(hdr+"\n".join(L)+"\n\nend C3.RV32\n")
