
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

400345a4 <mz_crc32>:
400345a4:	c1b1                	beqz	a1,400345e8 <mz_crc32+0x44>
400345a6:	3ff1d737          	lui	a4,0x3ff1d
400345aa:	fff54513          	not	a0,a0
400345ae:	962e                	add	a2,a2,a1
400345b0:	0e470713          	addi	a4,a4,228 # 3ff1d0e4 <s_crc32.2661>
400345b4:	00c59563          	bne	a1,a2,400345be <mz_crc32+0x1a>
400345b8:	fff54513          	not	a0,a0
400345bc:	8082                	ret
400345be:	0585                	addi	a1,a1,1
400345c0:	fff5c683          	lbu	a3,-1(a1)
400345c4:	00455793          	srli	a5,a0,0x4
400345c8:	8d35                	xor	a0,a0,a3
400345ca:	893d                	andi	a0,a0,15
400345cc:	050a                	slli	a0,a0,0x2
400345ce:	953a                	add	a0,a0,a4
400345d0:	4108                	lw	a0,0(a0)
400345d2:	8291                	srli	a3,a3,0x4
400345d4:	8fa9                	xor	a5,a5,a0
400345d6:	0047d513          	srli	a0,a5,0x4
400345da:	8bbd                	andi	a5,a5,15
400345dc:	8fb5                	xor	a5,a5,a3
400345de:	078a                	slli	a5,a5,0x2
400345e0:	97ba                	add	a5,a5,a4
400345e2:	439c                	lw	a5,0(a5)
400345e4:	8d3d                	xor	a0,a0,a5
400345e6:	b7f9                	j	400345b4 <mz_crc32+0x10>
400345e8:	4501                	li	a0,0
400345ea:	8082                	ret
