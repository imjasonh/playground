#!/usr/bin/env python3
"""Prints a `fetchRel` lemma for each instruction of one function, from
`llvm-objdump -d` output for it. `decide` checks each lemma against the
function's extracted bytes, so a wrong line fails the build.

Usage: decode-lemmas.py OBJDUMP_OUTPUT START_ADDRESS PREFIX CODE_NAME
"""
import re, sys
REGS = {'zero':0,'ra':1,'sp':2,'gp':3,'tp':4,'t0':5,'t1':6,'t2':7,'s0':8,'fp':8,'s1':9}
for i in range(8): REGS[f'a{i}'] = 10+i
for i in range(2,12): REGS[f's{i}'] = 16+i
for i in range(3,7): REGS[f't{i}'] = 25+i
NAMES = {0:'x0',1:'ra',2:'sp',10:'a0',11:'a1',12:'a2',13:'a3',14:'a4',15:'a5',16:'a6'}
def r(n): v=REGS[n]; return NAMES.get(v, f'({v} : Fin 32)')
def w(v): return f'0x{v & 0xFFFFFFFF:X}'
def imm(s): return int(s,0)
src, start, prefix, code = sys.argv[1], int(sys.argv[2],16), sys.argv[3], sys.argv[4]
ALU = {'add':'add','sub':'sub','and':'and','or':'or','xor':'xor','sltu':'sltu','slt':'slt','mul':'mul','mulhu':'mulhu','mulh':'mulh','sll':'sll','srl':'srl','sra':'sra'}
ALUI = {'addi':'add','andi':'and','ori':'or','xori':'xor','sltiu':'sltu','slti':'slt','slli':'sll','srli':'srl','srai':'sra'}
BR = {'beq','bne','bltu','bgeu','blt','bge'}
out=[]
for line in open(src):
    m = re.match(r'\s*([0-9a-f]+):\s+([0-9a-f]{4}|[0-9a-f]{8})\s+(\S+)\s*(.*)', line)
    if not m: continue
    addr = int(m.group(1),16); ln = len(m.group(2)) // 2
    op = m.group(3); args = [a.strip() for a in re.sub(r'<.*>','',m.group(4)).split(',') if a.strip()]
    off = addr - start
    def mem(a):
        mm = re.match(r'(-?0x[0-9a-f]+|-?\d+)\((\w+)\)', a); return imm(mm.group(1)), mm.group(2)
    if op in ALU: ins = f'.alu .{ALU[op]} {r(args[0])} {r(args[1])} {r(args[2])}'
    elif op in ALUI: ins = f'.aluImm .{ALUI[op]} {r(args[0])} {r(args[1])} {w(imm(args[2]))}'
    elif op == 'li': ins = f'.aluImm .add {r(args[0])} x0 {w(imm(args[1]))}'
    elif op == 'mv': ins = f'.alu .add {r(args[0])} x0 {r(args[1])}'
    elif op == 'not': ins = f'.aluImm .xor {r(args[0])} {r(args[1])} 0xFFFFFFFF'
    elif op == 'neg': ins = f'.alu .sub {r(args[0])} x0 {r(args[1])}'
    elif op == 'zext.b': ins = f'.aluImm .and {r(args[0])} {r(args[1])} 0xFF'
    elif op == 'seqz': ins = f'.aluImm .sltu {r(args[0])} {r(args[1])} 0x1'
    elif op == 'snez': ins = f'.alu .sltu {r(args[0])} x0 {r(args[1])}'
    elif op == 'lw': o,b = mem(args[1]); ins = f'.load .lw {r(args[0])} {r(b)} {w(o)}'
    elif op == 'lbu': o,b = mem(args[1]); ins = f'.load .lbu {r(args[0])} {r(b)} {w(o)}'
    elif op == 'lb': o,b = mem(args[1]); ins = f'.load .lb {r(args[0])} {r(b)} {w(o)}'
    elif op == 'sw': o,b = mem(args[1]); ins = f'.store .sw {r(b)} {r(args[0])} {w(o)}'
    elif op == 'sb': o,b = mem(args[1]); ins = f'.store .sb {r(b)} {r(args[0])} {w(o)}'
    elif op == 'lui': ins = f'.lui {r(args[0])} {w(imm(args[1]) << 12)}'
    elif op == 'auipc': ins = f'.auipc {r(args[0])} {w(imm(args[1]) << 12)}'
    elif op == 'jalr':
        if len(args) == 2: o,b = mem(args[1]); ins = f'.jalr {r(args[0])} {r(b)} {w(o)}'
        elif '(' in args[0]: o,b = mem(args[0]); ins = f'.jalr ra {r(b)} {w(o)}'
        else: ins = f'.jalr ra {r(args[0])} 0x0'
    elif op == 'jr':
        if '(' in args[0]: o,b = mem(args[0]); ins = f'.jalr x0 {r(b)} {w(o)}'
        else: ins = f'.jalr x0 {r(args[0])} 0x0'
    elif op == 'ret': ins = '.jalr x0 ra 0x0'
    elif op == 'j': ins = f'.jal x0 {w(imm(args[0]) - addr)}'
    elif op in BR: ins = f'.branch .{op} {r(args[0])} {r(args[1])} {w(imm(args[2]) - addr)}'
    elif op in ('beqz','bnez'): ins = f'.branch .{op[:3]} {r(args[0])} x0 {w(imm(args[1]) - addr)}'
    elif op == 'bltz': ins = f'.branch .blt {r(args[0])} x0 {w(imm(args[1]) - addr)}'
    elif op == 'bgez': ins = f'.branch .bge {r(args[0])} x0 {w(imm(args[1]) - addr)}'
    else: sys.exit(f'unknown {op} at {addr:x}: {line}')
    out.append(f'theorem {prefix}_at_{off:x} : fetchRel {code} 0x{off:X} = some ({ins}, {ln}) := by decide')
print('\n'.join(out))
