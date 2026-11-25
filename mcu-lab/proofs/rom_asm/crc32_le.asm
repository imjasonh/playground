
4004a29a <crc32_le>:
4004a29a:	3ff1d6b7          	lui	x13,0x3ff1d
4004a29e:	fff54513          	not	x10,x10
4004a2a2:	4701                	li	x14,0
4004a2a4:	9c868693          	addi	x13,x13,-1592 # 3ff1c9c8 <crc32_le_table>
4004a2a8:	00c71563          	bne	x14,x12,4004a2b2 <crc32_le+0x18>
4004a2ac:	fff54513          	not	x10,x10
4004a2b0:	8082                	ret
4004a2b2:	00e587b3          	add	x15,x11,x14
4004a2b6:	0007c783          	lbu	x15,0(x15)
4004a2ba:	0705                	addi	x14,x14,1
4004a2bc:	8fa9                	xor	x15,x15,x10
4004a2be:	0ff7f793          	zext.b	x15,x15
4004a2c2:	078a                	slli	x15,x15,0x2
4004a2c4:	97b6                	add	x15,x15,x13
4004a2c6:	439c                	lw	x15,0(x15)
4004a2c8:	8121                	srli	x10,x10,0x8
4004a2ca:	8d3d                	xor	x10,x10,x15
4004a2cc:	bff1                	j	4004a2a8 <crc32_le+0xe>
