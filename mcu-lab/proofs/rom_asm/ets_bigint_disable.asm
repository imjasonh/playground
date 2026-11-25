
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .text:

400461ca <ets_bigint_disable>:
400461ca:	600c07b7          	lui	a5,0x600c0
400461ce:	5f98                	lw	a4,56(a5)
400461d0:	00176713          	ori	a4,a4,1
400461d4:	df98                	sw	a4,56(a5)
400461d6:	4fd8                	lw	a4,28(a5)
400461d8:	00876713          	ori	a4,a4,8
400461dc:	cfd8                	sw	a4,28(a5)
400461de:	4bd8                	lw	a4,20(a5)
400461e0:	9b5d                	andi	a4,a4,-9
400461e2:	cbd8                	sw	a4,20(a5)
400461e4:	8082                	ret
