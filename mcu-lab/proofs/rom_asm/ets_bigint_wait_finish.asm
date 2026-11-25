
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .text:

40046288 <ets_bigint_wait_finish>:
40046288:	6003d7b7          	lui	a5,0x6003d
4004628c:	4705                	li	a4,1
4004628e:	8187a683          	lw	a3,-2024(a5) # 6003c818 <SPIMEM0+0x39818>
40046292:	fee69ee3          	bne	a3,a4,4004628e <ets_bigint_wait_finish+0x6>
40046296:	80e7ae23          	sw	a4,-2020(a5)
4004629a:	8082                	ret
