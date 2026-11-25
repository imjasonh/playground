
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .text:

40046270 <ets_bigint_modexp>:
40046270:	88c2                	mv	a7,a6
40046272:	883e                	mv	a6,a5
40046274:	87ba                	mv	a5,a4
40046276:	8736                	mv	a4,a3
40046278:	86b2                	mv	a3,a2
4004627a:	862e                	mv	a2,a1
4004627c:	85aa                	mv	a1,a0
4004627e:	6003d537          	lui	a0,0x6003d
40046282:	80c50513          	addi	a0,a0,-2036 # 6003c80c <SPIMEM0+0x3980c>
40046286:	bda5                	j	400460fe <ets_bigint_modcommon>
