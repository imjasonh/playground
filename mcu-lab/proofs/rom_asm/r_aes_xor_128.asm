
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

40002be6 <r_aes_xor_128>:
40002be6:	16fd                	addi	a3,a3,-1
40002be8:	06e2                	slli	a3,a3,0x18
40002bea:	86e1                	srai	a3,a3,0x18
40002bec:	01869793          	slli	a5,a3,0x18
40002bf0:	87e1                	srai	a5,a5,0x18
40002bf2:	0007d363          	bgez	a5,40002bf8 <r_aes_xor_128+0x12>
40002bf6:	8082                	ret
40002bf8:	00d587b3          	add	a5,a1,a3
40002bfc:	00d60833          	add	a6,a2,a3
40002c00:	0007c783          	lbu	a5,0(a5)
40002c04:	00084803          	lbu	a6,0(a6)
40002c08:	00d50733          	add	a4,a0,a3
40002c0c:	16fd                	addi	a3,a3,-1
40002c0e:	0107c7b3          	xor	a5,a5,a6
40002c12:	00f70023          	sb	a5,0(a4)
40002c16:	bfd9                	j	40002bec <r_aes_xor_128+0x6>
