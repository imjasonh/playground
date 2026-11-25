
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .text:

4004629c <ets_bigint_getz>:
4004629c:	06000793          	li	a5,96
400462a0:	02b7e363          	bltu	a5,a1,400462c6 <ets_bigint_getz+0x2a>
400462a4:	4785                	li	a5,1
400462a6:	c10d                	beqz	a0,400462c8 <ets_bigint_getz+0x2c>
400462a8:	00259613          	slli	a2,a1,0x2
400462ac:	6003c5b7          	lui	a1,0x6003c
400462b0:	1141                	addi	sp,sp,-16
400462b2:	20058593          	addi	a1,a1,512 # 6003c200 <SPIMEM0+0x39200>
400462b6:	c606                	sw	ra,12(sp)
400462b8:	502120ef          	jal	400587ba <memcpy>
400462bc:	40b2                	lw	ra,12(sp)
400462be:	4781                	li	a5,0
400462c0:	853e                	mv	a0,a5
400462c2:	0141                	addi	sp,sp,16
400462c4:	8082                	ret
400462c6:	4785                	li	a5,1
400462c8:	853e                	mv	a0,a5
400462ca:	8082                	ret
