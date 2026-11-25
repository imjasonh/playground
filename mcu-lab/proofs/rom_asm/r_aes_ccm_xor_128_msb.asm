
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

40001f84 <r_aes_ccm_xor_128_msb>:
40001f84:	4781                	li	a5,0
40001f86:	483d                	li	a6,15
40001f88:	00d7c363          	blt	a5,a3,40001f8e <r_aes_ccm_xor_128_msb+0xa>
40001f8c:	8082                	ret
40001f8e:	40f80733          	sub	a4,a6,a5
40001f92:	00f58333          	add	t1,a1,a5
40001f96:	9732                	add	a4,a4,a2
40001f98:	00074703          	lbu	a4,0(a4)
40001f9c:	00034303          	lbu	t1,0(t1)
40001fa0:	00f508b3          	add	a7,a0,a5
40001fa4:	0785                	addi	a5,a5,1
40001fa6:	00674733          	xor	a4,a4,t1
40001faa:	07e2                	slli	a5,a5,0x18
40001fac:	00e88023          	sb	a4,0(a7)
40001fb0:	87e1                	srai	a5,a5,0x18
40001fb2:	bfd9                	j	40001f88 <r_aes_ccm_xor_128_msb+0x4>
