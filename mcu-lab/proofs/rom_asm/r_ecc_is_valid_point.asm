
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

40005f76 <r_ecc_is_valid_point>:
40005f76:	714d                	addi	sp,sp,-336
40005f78:	14912223          	sw	s1,324(sp)
40005f7c:	15212023          	sw	s2,320(sp)
40005f80:	84aa                	mv	s1,a0
40005f82:	892e                	mv	s2,a1
40005f84:	02200613          	li	a2,34
40005f88:	4581                	li	a1,0
40005f8a:	0068                	addi	a0,sp,12
40005f8c:	14112623          	sw	ra,332(sp)
40005f90:	14812423          	sw	s0,328(sp)
40005f94:	14b520ef          	jal	400588de <memset>
40005f98:	02200613          	li	a2,34
40005f9c:	4581                	li	a1,0
40005f9e:	1828                	addi	a0,sp,56
40005fa0:	d802                	sw	zero,48(sp)
40005fa2:	da02                	sw	zero,52(sp)
40005fa4:	13b520ef          	jal	400588de <memset>
40005fa8:	02200613          	li	a2,34
40005fac:	4581                	li	a1,0
40005fae:	10c8                	addi	a0,sp,100
40005fb0:	ce82                	sw	zero,92(sp)
40005fb2:	d082                	sw	zero,96(sp)
40005fb4:	12b520ef          	jal	400588de <memset>
40005fb8:	02200613          	li	a2,34
40005fbc:	4581                	li	a1,0
40005fbe:	0908                	addi	a0,sp,144
40005fc0:	c502                	sw	zero,136(sp)
40005fc2:	c702                	sw	zero,140(sp)
40005fc4:	11b520ef          	jal	400588de <memset>
40005fc8:	02200613          	li	a2,34
40005fcc:	4581                	li	a1,0
40005fce:	1968                	addi	a0,sp,188
40005fd0:	db02                	sw	zero,180(sp)
40005fd2:	dd02                	sw	zero,184(sp)
40005fd4:	10b520ef          	jal	400588de <memset>
40005fd8:	02200613          	li	a2,34
40005fdc:	4581                	li	a1,0
40005fde:	11a8                	addi	a0,sp,232
40005fe0:	d182                	sw	zero,224(sp)
40005fe2:	d382                	sw	zero,228(sp)
40005fe4:	0fb520ef          	jal	400588de <memset>
40005fe8:	02200613          	li	a2,34
40005fec:	4581                	li	a1,0
40005fee:	0a48                	addi	a0,sp,276
40005ff0:	3fce0437          	lui	s0,0x3fce0
40005ff4:	10012623          	sw	zero,268(sp)
40005ff8:	10012823          	sw	zero,272(sp)
40005ffc:	0e3520ef          	jal	400588de <memset>
40006000:	f8842783          	lw	a5,-120(s0) # 3fcdff88 <r_modules_funcs_p>
40006004:	0070                	addi	a2,sp,12
40006006:	85ca                	mv	a1,s2
40006008:	39c7a783          	lw	a5,924(a5)
4000600c:	854a                	mv	a0,s2
4000600e:	12012c23          	sw	zero,312(sp)
40006012:	12012e23          	sw	zero,316(sp)
40006016:	9782                	jalr	a5
40006018:	f8842783          	lw	a5,-120(s0)
4000601c:	1830                	addi	a2,sp,56
4000601e:	85a6                	mv	a1,s1
40006020:	39c7a783          	lw	a5,924(a5)
40006024:	8526                	mv	a0,s1
40006026:	9782                	jalr	a5
40006028:	f8842783          	lw	a5,-120(s0)
4000602c:	10d0                	addi	a2,sp,100
4000602e:	182c                	addi	a1,sp,56
40006030:	39c7a783          	lw	a5,924(a5)
40006034:	8526                	mv	a0,s1
40006036:	9782                	jalr	a5
40006038:	f8842783          	lw	a5,-120(s0)
4000603c:	0910                	addi	a2,sp,144
4000603e:	85a6                	mv	a1,s1
40006040:	3547a783          	lw	a5,852(a5)
40006044:	8526                	mv	a0,s1
40006046:	9782                	jalr	a5
40006048:	f8842783          	lw	a5,-120(s0)
4000604c:	1970                	addi	a2,sp,188
4000604e:	85a6                	mv	a1,s1
40006050:	3547a783          	lw	a5,852(a5)
40006054:	0908                	addi	a0,sp,144
40006056:	9782                	jalr	a5
40006058:	f8842783          	lw	a5,-120(s0)
4000605c:	11b0                	addi	a2,sp,232
4000605e:	196c                	addi	a1,sp,188
40006060:	3b07a783          	lw	a5,944(a5)
40006064:	10c8                	addi	a0,sp,100
40006066:	9782                	jalr	a5
40006068:	f8842783          	lw	a5,-120(s0)
4000606c:	3ff1f5b7          	lui	a1,0x3ff1f
40006070:	0a50                	addi	a2,sp,276
40006072:	3547a783          	lw	a5,852(a5)
40006076:	11a8                	addi	a0,sp,232
40006078:	67058593          	addi	a1,a1,1648 # 3ff1f670 <coef_B>
4000607c:	9782                	jalr	a5
4000607e:	0a4c                	addi	a1,sp,276
40006080:	0068                	addi	a0,sp,12
40006082:	02200613          	li	a2,34
40006086:	6ec520ef          	jal	40058772 <memcmp>
4000608a:	14c12083          	lw	ra,332(sp)
4000608e:	14812403          	lw	s0,328(sp)
40006092:	14412483          	lw	s1,324(sp)
40006096:	14012903          	lw	s2,320(sp)
4000609a:	00153513          	seqz	a0,a0
4000609e:	6171                	addi	sp,sp,336
400060a0:	8082                	ret
