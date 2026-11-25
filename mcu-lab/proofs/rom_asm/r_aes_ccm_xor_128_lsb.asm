
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

40001f4c <r_aes_ccm_xor_128_lsb>:
40001f4c:	47bd                	li	a5,15
40001f4e:	40e78733          	sub	a4,a5,a4
40001f52:	0ff77713          	zext.b	a4,a4
40001f56:	4781                	li	a5,0
40001f58:	00d7c363          	blt	a5,a3,40001f5e <r_aes_ccm_xor_128_lsb+0x12>
40001f5c:	8082                	ret
40001f5e:	40f70833          	sub	a6,a4,a5
40001f62:	010508b3          	add	a7,a0,a6
40001f66:	00f60333          	add	t1,a2,a5
40001f6a:	982e                	add	a6,a6,a1
40001f6c:	00084803          	lbu	a6,0(a6)
40001f70:	00034303          	lbu	t1,0(t1)
40001f74:	0785                	addi	a5,a5,1
40001f76:	07e2                	slli	a5,a5,0x18
40001f78:	00684833          	xor	a6,a6,t1
40001f7c:	01088023          	sb	a6,0(a7)
40001f80:	87e1                	srai	a5,a5,0x18
40001f82:	bfd9                	j	40001f58 <r_aes_ccm_xor_128_lsb+0xc>
