
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .text:

400460fe <ets_bigint_modcommon>:
400460fe:	7179                	addi	sp,sp,-48
40046100:	c462                	sw	s8,8(sp)
40046102:	d606                	sw	ra,44(sp)
40046104:	d422                	sw	s0,40(sp)
40046106:	d226                	sw	s1,36(sp)
40046108:	d04a                	sw	s2,32(sp)
4004610a:	ce4e                	sw	s3,28(sp)
4004610c:	cc52                	sw	s4,24(sp)
4004610e:	ca56                	sw	s5,20(sp)
40046110:	c85a                	sw	s6,16(sp)
40046112:	c65e                	sw	s7,12(sp)
40046114:	fff88c13          	addi	s8,a7,-1
40046118:	05f00313          	li	t1,95
4004611c:	09836163          	bltu	t1,s8,4004619e <ets_bigint_modcommon+0xa0>
40046120:	4305                	li	t1,1
40046122:	c1ad                	beqz	a1,40046184 <ets_bigint_modcommon+0x86>
40046124:	c225                	beqz	a2,40046184 <ets_bigint_modcommon+0x86>
40046126:	ceb9                	beqz	a3,40046184 <ets_bigint_modcommon+0x86>
40046128:	cfb1                	beqz	a5,40046184 <ets_bigint_modcommon+0x86>
4004612a:	00289413          	slli	s0,a7,0x2
4004612e:	6003cbb7          	lui	s7,0x6003c
40046132:	89b2                	mv	s3,a2
40046134:	8a2a                	mv	s4,a0
40046136:	8622                	mv	a2,s0
40046138:	600b8513          	addi	a0,s7,1536 # 6003c600 <SPIMEM0+0x39600>
4004613c:	84be                	mv	s1,a5
4004613e:	8b42                	mv	s6,a6
40046140:	8aba                	mv	s5,a4
40046142:	8936                	mv	s2,a3
40046144:	676120ef          	jal	400587ba <memcpy>
40046148:	8622                	mv	a2,s0
4004614a:	85ce                	mv	a1,s3
4004614c:	400b8513          	addi	a0,s7,1024
40046150:	66a120ef          	jal	400587ba <memcpy>
40046154:	8622                	mv	a2,s0
40046156:	85ca                	mv	a1,s2
40046158:	6003c537          	lui	a0,0x6003c
4004615c:	65e120ef          	jal	400587ba <memcpy>
40046160:	8622                	mv	a2,s0
40046162:	85a6                	mv	a1,s1
40046164:	200b8513          	addi	a0,s7,512
40046168:	652120ef          	jal	400587ba <memcpy>
4004616c:	6003d7b7          	lui	a5,0x6003d
40046170:	8367a023          	sw	s6,-2016(a5) # 6003c820 <SPIMEM0+0x39820>
40046174:	8157a023          	sw	s5,-2048(a5)
40046178:	8187a223          	sw	s8,-2044(a5)
4004617c:	4785                	li	a5,1
4004617e:	00fa2023          	sw	a5,0(s4)
40046182:	4301                	li	t1,0
40046184:	50b2                	lw	ra,44(sp)
40046186:	5422                	lw	s0,40(sp)
40046188:	5492                	lw	s1,36(sp)
4004618a:	5902                	lw	s2,32(sp)
4004618c:	49f2                	lw	s3,28(sp)
4004618e:	4a62                	lw	s4,24(sp)
40046190:	4ad2                	lw	s5,20(sp)
40046192:	4b42                	lw	s6,16(sp)
40046194:	4bb2                	lw	s7,12(sp)
40046196:	4c22                	lw	s8,8(sp)
40046198:	851a                	mv	a0,t1
4004619a:	6145                	addi	sp,sp,48
4004619c:	8082                	ret
4004619e:	4305                	li	t1,1
400461a0:	b7d5                	j	40046184 <ets_bigint_modcommon+0x86>
