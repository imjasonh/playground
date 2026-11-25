
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .text:

40058772 <memcmp>:
40058772:	478d                	li	a5,3
40058774:	02c7f063          	bgeu	a5,a2,40058794 <memcmp+0x22>
40058778:	00b567b3          	or	a5,a0,a1
4005877c:	8b8d                	andi	a5,a5,3
4005877e:	eb99                	bnez	a5,40058794 <memcmp+0x22>
40058780:	478d                	li	a5,3
40058782:	4114                	lw	a3,0(a0)
40058784:	4198                	lw	a4,0(a1)
40058786:	00e69763          	bne	a3,a4,40058794 <memcmp+0x22>
4005878a:	1671                	addi	a2,a2,-4
4005878c:	0511                	addi	a0,a0,4
4005878e:	0591                	addi	a1,a1,4
40058790:	fec7e9e3          	bltu	a5,a2,40058782 <memcmp+0x10>
40058794:	4701                	li	a4,0
40058796:	00e61463          	bne	a2,a4,4005879e <memcmp+0x2c>
4005879a:	4501                	li	a0,0
4005879c:	8082                	ret
4005879e:	00e507b3          	add	a5,a0,a4
400587a2:	0705                	addi	a4,a4,1
400587a4:	00e586b3          	add	a3,a1,a4
400587a8:	0007c783          	lbu	a5,0(a5)
400587ac:	fff6c683          	lbu	a3,-1(a3)
400587b0:	fed783e3          	beq	a5,a3,40058796 <memcmp+0x24>
400587b4:	40d78533          	sub	a0,a5,a3
400587b8:	8082                	ret
