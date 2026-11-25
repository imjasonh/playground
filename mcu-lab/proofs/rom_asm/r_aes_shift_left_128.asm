
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

40002c18 <r_aes_shift_left_128>:
40002c18:	00e50693          	addi	a3,a0,14
40002c1c:	00f58713          	addi	a4,a1,15
40002c20:	0016c783          	lbu	a5,1(a3)
40002c24:	0006c603          	lbu	a2,0(a3)
40002c28:	177d                	addi	a4,a4,-1
40002c2a:	0786                	slli	a5,a5,0x1
40002c2c:	821d                	srli	a2,a2,0x7
40002c2e:	8fd1                	or	a5,a5,a2
40002c30:	00f700a3          	sb	a5,1(a4)
40002c34:	16fd                	addi	a3,a3,-1
40002c36:	fee595e3          	bne	a1,a4,40002c20 <r_aes_shift_left_128+0x8>
40002c3a:	00054783          	lbu	a5,0(a0)
40002c3e:	0786                	slli	a5,a5,0x1
40002c40:	00f58023          	sb	a5,0(a1)
40002c44:	8082                	ret
