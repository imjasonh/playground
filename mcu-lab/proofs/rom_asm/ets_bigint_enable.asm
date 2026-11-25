
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .text:

400461a2 <ets_bigint_enable>:
400461a2:	600c07b7          	lui	a5,0x600c0
400461a6:	4bd8                	lw	a4,20(a5)
400461a8:	6003d6b7          	lui	a3,0x6003d
400461ac:	00876713          	ori	a4,a4,8
400461b0:	cbd8                	sw	a4,20(a5)
400461b2:	4fd8                	lw	a4,28(a5)
400461b4:	9b1d                	andi	a4,a4,-25
400461b6:	cfd8                	sw	a4,28(a5)
400461b8:	5f98                	lw	a4,56(a5)
400461ba:	9b79                	andi	a4,a4,-2
400461bc:	df98                	sw	a4,56(a5)
400461be:	4785                	li	a5,1
400461c0:	8086a703          	lw	a4,-2040(a3) # 6003c808 <SPIMEM0+0x39808>
400461c4:	fef71ee3          	bne	a4,a5,400461c0 <ets_bigint_enable+0x1e>
400461c8:	8082                	ret
