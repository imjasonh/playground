
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

40005abc <r_ecc_point_multiplication_win_256>:
40005abc:	7169                	addi	sp,sp,-304
40005abe:	12812423          	sw	s0,296(sp)
40005ac2:	12112623          	sw	ra,300(sp)
40005ac6:	12912223          	sw	s1,292(sp)
40005aca:	13212023          	sw	s2,288(sp)
40005ace:	11312e23          	sw	s3,284(sp)
40005ad2:	11412c23          	sw	s4,280(sp)
40005ad6:	11512a23          	sw	s5,276(sp)
40005ada:	14454903          	lbu	s2,324(a0)
40005ade:	4705                	li	a4,1
40005ae0:	842a                	mv	s0,a0
40005ae2:	fff90793          	addi	a5,s2,-1
40005ae6:	0ff7f793          	zext.b	a5,a5
40005aea:	14255583          	lhu	a1,322(a0)
40005aee:	1ef76263          	bltu	a4,a5,40005cd2 <r_ecc_point_multiplication_win_256+0x216>
40005af2:	1ae90963          	beq	s2,a4,40005ca4 <r_ecc_point_multiplication_win_256+0x1e8>
40005af6:	14852903          	lw	s2,328(a0)
40005afa:	07f00693          	li	a3,127
40005afe:	4541                	li	a0,16
40005b00:	8e8d                	sub	a3,a3,a1
40005b02:	02a6c6b3          	div	a3,a3,a0
40005b06:	03f00793          	li	a5,63
40005b0a:	8f8d                	sub	a5,a5,a1
40005b0c:	00f5f613          	andi	a2,a1,15
40005b10:	00840493          	addi	s1,s0,8
40005b14:	02a7c7b3          	div	a5,a5,a0
40005b18:	08968693          	addi	a3,a3,137
40005b1c:	0686                	slli	a3,a3,0x1
40005b1e:	96a2                	add	a3,a3,s0
40005b20:	0006d703          	lhu	a4,0(a3)
40005b24:	0bf00693          	li	a3,191
40005b28:	8e8d                	sub	a3,a3,a1
40005b2a:	40c75733          	sra	a4,a4,a2
40005b2e:	8b05                	andi	a4,a4,1
40005b30:	02a6c6b3          	div	a3,a3,a0
40005b34:	08978793          	addi	a5,a5,137
40005b38:	0786                	slli	a5,a5,0x1
40005b3a:	97a2                	add	a5,a5,s0
40005b3c:	0007d783          	lhu	a5,0(a5)
40005b40:	40c7d7b3          	sra	a5,a5,a2
40005b44:	8b85                	andi	a5,a5,1
40005b46:	0786                	slli	a5,a5,0x1
40005b48:	97ba                	add	a5,a5,a4
40005b4a:	0786                	slli	a5,a5,0x1
40005b4c:	08968693          	addi	a3,a3,137
40005b50:	0686                	slli	a3,a3,0x1
40005b52:	96a2                	add	a3,a3,s0
40005b54:	0006d703          	lhu	a4,0(a3)
40005b58:	40c75733          	sra	a4,a4,a2
40005b5c:	8b05                	andi	a4,a4,1
40005b5e:	97ba                	add	a5,a5,a4
40005b60:	0ff00713          	li	a4,255
40005b64:	8f0d                	sub	a4,a4,a1
40005b66:	02a74733          	div	a4,a4,a0
40005b6a:	0786                	slli	a5,a5,0x1
40005b6c:	08970713          	addi	a4,a4,137
40005b70:	0706                	slli	a4,a4,0x1
40005b72:	9722                	add	a4,a4,s0
40005b74:	00075703          	lhu	a4,0(a4)
40005b78:	40c75633          	sra	a2,a4,a2
40005b7c:	8a05                	andi	a2,a2,1
40005b7e:	97b2                	add	a5,a5,a2
40005b80:	cfc5                	beqz	a5,40005c38 <r_ecc_point_multiplication_win_256+0x17c>
40005b82:	08400713          	li	a4,132
40005b86:	02e787b3          	mul	a5,a5,a4
40005b8a:	02200613          	li	a2,34
40005b8e:	0028                	addi	a0,sp,8
40005b90:	f7c78793          	addi	a5,a5,-132
40005b94:	993e                	add	s2,s2,a5
40005b96:	85ca                	mv	a1,s2
40005b98:	423520ef          	jal	400587ba <memcpy>
40005b9c:	02492783          	lw	a5,36(s2)
40005ba0:	02200613          	li	a2,34
40005ba4:	02c90593          	addi	a1,s2,44
40005ba8:	d63e                	sw	a5,44(sp)
40005baa:	02892783          	lw	a5,40(s2)
40005bae:	1848                	addi	a0,sp,52
40005bb0:	d83e                	sw	a5,48(sp)
40005bb2:	409520ef          	jal	400587ba <memcpy>
40005bb6:	05092783          	lw	a5,80(s2)
40005bba:	02200613          	li	a2,34
40005bbe:	05890593          	addi	a1,s2,88
40005bc2:	ccbe                	sw	a5,88(sp)
40005bc4:	05492783          	lw	a5,84(s2)
40005bc8:	1088                	addi	a0,sp,96
40005bca:	cebe                	sw	a5,92(sp)
40005bcc:	3ef520ef          	jal	400587ba <memcpy>
40005bd0:	07c92783          	lw	a5,124(s2)
40005bd4:	0170                	addi	a2,sp,140
40005bd6:	85a6                	mv	a1,s1
40005bd8:	c33e                	sw	a5,132(sp)
40005bda:	08092783          	lw	a5,128(s2)
40005bde:	0028                	addi	a0,sp,8
40005be0:	c53e                	sw	a5,136(sp)
40005be2:	3fce07b7          	lui	a5,0x3fce0
40005be6:	f887a783          	lw	a5,-120(a5) # 3fcdff88 <r_modules_funcs_p>
40005bea:	3887a783          	lw	a5,904(a5)
40005bee:	9782                	jalr	a5
40005bf0:	02200613          	li	a2,34
40005bf4:	016c                	addi	a1,sp,140
40005bf6:	8526                	mv	a0,s1
40005bf8:	3c3520ef          	jal	400587ba <memcpy>
40005bfc:	57ca                	lw	a5,176(sp)
40005bfe:	02200613          	li	a2,34
40005c02:	192c                	addi	a1,sp,184
40005c04:	d45c                	sw	a5,44(s0)
40005c06:	57da                	lw	a5,180(sp)
40005c08:	03440513          	addi	a0,s0,52
40005c0c:	d81c                	sw	a5,48(s0)
40005c0e:	3ad520ef          	jal	400587ba <memcpy>
40005c12:	47fe                	lw	a5,220(sp)
40005c14:	02200613          	li	a2,34
40005c18:	11cc                	addi	a1,sp,228
40005c1a:	cc3c                	sw	a5,88(s0)
40005c1c:	578e                	lw	a5,224(sp)
40005c1e:	06040513          	addi	a0,s0,96
40005c22:	cc7c                	sw	a5,92(s0)
40005c24:	397520ef          	jal	400587ba <memcpy>
40005c28:	10812783          	lw	a5,264(sp)
40005c2c:	08f42223          	sw	a5,132(s0)
40005c30:	10c12783          	lw	a5,268(sp)
40005c34:	08f42423          	sw	a5,136(s0)
40005c38:	14245783          	lhu	a5,322(s0)
40005c3c:	cbad                	beqz	a5,40005cae <r_ecc_point_multiplication_win_256+0x1f2>
40005c3e:	3fce07b7          	lui	a5,0x3fce0
40005c42:	f887a783          	lw	a5,-120(a5) # 3fcdff88 <r_modules_funcs_p>
40005c46:	016c                	addi	a1,sp,140
40005c48:	8526                	mv	a0,s1
40005c4a:	38c7a783          	lw	a5,908(a5)
40005c4e:	9782                	jalr	a5
40005c50:	02200613          	li	a2,34
40005c54:	016c                	addi	a1,sp,140
40005c56:	8526                	mv	a0,s1
40005c58:	363520ef          	jal	400587ba <memcpy>
40005c5c:	57ca                	lw	a5,176(sp)
40005c5e:	02200613          	li	a2,34
40005c62:	192c                	addi	a1,sp,184
40005c64:	d45c                	sw	a5,44(s0)
40005c66:	57da                	lw	a5,180(sp)
40005c68:	03440513          	addi	a0,s0,52
40005c6c:	d81c                	sw	a5,48(s0)
40005c6e:	34d520ef          	jal	400587ba <memcpy>
40005c72:	47fe                	lw	a5,220(sp)
40005c74:	02200613          	li	a2,34
40005c78:	11cc                	addi	a1,sp,228
40005c7a:	cc3c                	sw	a5,88(s0)
40005c7c:	578e                	lw	a5,224(sp)
40005c7e:	06040513          	addi	a0,s0,96
40005c82:	cc7c                	sw	a5,92(s0)
40005c84:	337520ef          	jal	400587ba <memcpy>
40005c88:	10812783          	lw	a5,264(sp)
40005c8c:	08f42223          	sw	a5,132(s0)
40005c90:	10c12783          	lw	a5,268(sp)
40005c94:	08f42423          	sw	a5,136(s0)
40005c98:	14245783          	lhu	a5,322(s0)
40005c9c:	17fd                	addi	a5,a5,-1
40005c9e:	14f41123          	sh	a5,322(s0)
40005ca2:	a801                	j	40005cb2 <r_ecc_point_multiplication_win_256+0x1f6>
40005ca4:	3ff1f937          	lui	s2,0x3ff1f
40005ca8:	7a090913          	addi	s2,s2,1952 # 3ff1f7a0 <ECC_4Win_Look_up_table>
40005cac:	b5b9                	j	40005afa <r_ecc_point_multiplication_win_256+0x3e>
40005cae:	00042223          	sw	zero,4(s0)
40005cb2:	12c12083          	lw	ra,300(sp)
40005cb6:	12812403          	lw	s0,296(sp)
40005cba:	12412483          	lw	s1,292(sp)
40005cbe:	12012903          	lw	s2,288(sp)
40005cc2:	11c12983          	lw	s3,284(sp)
40005cc6:	11812a03          	lw	s4,280(sp)
40005cca:	11412a83          	lw	s5,276(sp)
40005cce:	6155                	addi	sp,sp,304
40005cd0:	8082                	ret
40005cd2:	478d                	li	a5,3
40005cd4:	1af91d63          	bne	s2,a5,40005e8e <r_ecc_point_multiplication_win_256+0x3d2>
40005cd8:	3fce07b7          	lui	a5,0x3fce0
40005cdc:	f887a783          	lw	a5,-120(a5) # 3fcdff88 <r_modules_funcs_p>
40005ce0:	08c50993          	addi	s3,a0,140
40005ce4:	002c                	addi	a1,sp,8
40005ce6:	38c7a783          	lw	a5,908(a5)
40005cea:	854e                	mv	a0,s3
40005cec:	0b840a93          	addi	s5,s0,184
40005cf0:	9782                	jalr	a5
40005cf2:	02200613          	li	a2,34
40005cf6:	002c                	addi	a1,sp,8
40005cf8:	854e                	mv	a0,s3
40005cfa:	2c1520ef          	jal	400587ba <memcpy>
40005cfe:	57b2                	lw	a5,44(sp)
40005d00:	02200613          	li	a2,34
40005d04:	184c                	addi	a1,sp,52
40005d06:	0af42823          	sw	a5,176(s0)
40005d0a:	57c2                	lw	a5,48(sp)
40005d0c:	8556                	mv	a0,s5
40005d0e:	0e440a13          	addi	s4,s0,228
40005d12:	0af42a23          	sw	a5,180(s0)
40005d16:	2a5520ef          	jal	400587ba <memcpy>
40005d1a:	47e6                	lw	a5,88(sp)
40005d1c:	02200613          	li	a2,34
40005d20:	108c                	addi	a1,sp,96
40005d22:	0cf42e23          	sw	a5,220(s0)
40005d26:	47f6                	lw	a5,92(sp)
40005d28:	8552                	mv	a0,s4
40005d2a:	0ef42023          	sw	a5,224(s0)
40005d2e:	28d520ef          	jal	400587ba <memcpy>
40005d32:	479a                	lw	a5,132(sp)
40005d34:	04000713          	li	a4,64
40005d38:	10f42423          	sw	a5,264(s0)
40005d3c:	47aa                	lw	a5,136(sp)
40005d3e:	10f42623          	sw	a5,268(s0)
40005d42:	14245783          	lhu	a5,322(s0)
40005d46:	0785                	addi	a5,a5,1
40005d48:	07c2                	slli	a5,a5,0x10
40005d4a:	83c1                	srli	a5,a5,0x10
40005d4c:	14f41123          	sh	a5,322(s0)
40005d50:	06e79263          	bne	a5,a4,40005db4 <r_ecc_point_multiplication_win_256+0x2f8>
40005d54:	14842483          	lw	s1,328(s0)
40005d58:	02200613          	li	a2,34
40005d5c:	85ce                	mv	a1,s3
40005d5e:	08448513          	addi	a0,s1,132
40005d62:	259520ef          	jal	400587ba <memcpy>
40005d66:	0b042783          	lw	a5,176(s0)
40005d6a:	02200613          	li	a2,34
40005d6e:	85d6                	mv	a1,s5
40005d70:	0af4a423          	sw	a5,168(s1)
40005d74:	0b442783          	lw	a5,180(s0)
40005d78:	0b048513          	addi	a0,s1,176
40005d7c:	0af4a623          	sw	a5,172(s1)
40005d80:	23b520ef          	jal	400587ba <memcpy>
40005d84:	0dc42783          	lw	a5,220(s0)
40005d88:	02200613          	li	a2,34
40005d8c:	85d2                	mv	a1,s4
40005d8e:	0cf4aa23          	sw	a5,212(s1)
40005d92:	0e042783          	lw	a5,224(s0)
40005d96:	0dc48513          	addi	a0,s1,220
40005d9a:	0cf4ac23          	sw	a5,216(s1)
40005d9e:	21d520ef          	jal	400587ba <memcpy>
40005da2:	10842783          	lw	a5,264(s0)
40005da6:	10f4a023          	sw	a5,256(s1)
40005daa:	10c42783          	lw	a5,268(s0)
40005dae:	10f4a223          	sw	a5,260(s1)
40005db2:	b701                	j	40005cb2 <r_ecc_point_multiplication_win_256+0x1f6>
40005db4:	08000713          	li	a4,128
40005db8:	06e79263          	bne	a5,a4,40005e1c <r_ecc_point_multiplication_win_256+0x360>
40005dbc:	14842483          	lw	s1,328(s0)
40005dc0:	02200613          	li	a2,34
40005dc4:	85ce                	mv	a1,s3
40005dc6:	18c48513          	addi	a0,s1,396
40005dca:	1f1520ef          	jal	400587ba <memcpy>
40005dce:	0b042783          	lw	a5,176(s0)
40005dd2:	02200613          	li	a2,34
40005dd6:	85d6                	mv	a1,s5
40005dd8:	1af4a823          	sw	a5,432(s1)
40005ddc:	0b442783          	lw	a5,180(s0)
40005de0:	1b848513          	addi	a0,s1,440
40005de4:	1af4aa23          	sw	a5,436(s1)
40005de8:	1d3520ef          	jal	400587ba <memcpy>
40005dec:	0dc42783          	lw	a5,220(s0)
40005df0:	02200613          	li	a2,34
40005df4:	85d2                	mv	a1,s4
40005df6:	1cf4ae23          	sw	a5,476(s1)
40005dfa:	0e042783          	lw	a5,224(s0)
40005dfe:	1e448513          	addi	a0,s1,484
40005e02:	1ef4a023          	sw	a5,480(s1)
40005e06:	1b5520ef          	jal	400587ba <memcpy>
40005e0a:	10842783          	lw	a5,264(s0)
40005e0e:	20f4a423          	sw	a5,520(s1)
40005e12:	10c42783          	lw	a5,268(s0)
40005e16:	20f4a623          	sw	a5,524(s1)
40005e1a:	bd61                	j	40005cb2 <r_ecc_point_multiplication_win_256+0x1f6>
40005e1c:	0c000713          	li	a4,192
40005e20:	e8e799e3          	bne	a5,a4,40005cb2 <r_ecc_point_multiplication_win_256+0x1f6>
40005e24:	14842483          	lw	s1,328(s0)
40005e28:	02200613          	li	a2,34
40005e2c:	85ce                	mv	a1,s3
40005e2e:	39c48513          	addi	a0,s1,924
40005e32:	189520ef          	jal	400587ba <memcpy>
40005e36:	0b042783          	lw	a5,176(s0)
40005e3a:	02200613          	li	a2,34
40005e3e:	85d6                	mv	a1,s5
40005e40:	3cf4a023          	sw	a5,960(s1)
40005e44:	0b442783          	lw	a5,180(s0)
40005e48:	3c848513          	addi	a0,s1,968
40005e4c:	3cf4a223          	sw	a5,964(s1)
40005e50:	16b520ef          	jal	400587ba <memcpy>
40005e54:	0dc42783          	lw	a5,220(s0)
40005e58:	02200613          	li	a2,34
40005e5c:	85d2                	mv	a1,s4
40005e5e:	3ef4a623          	sw	a5,1004(s1)
40005e62:	0e042783          	lw	a5,224(s0)
40005e66:	3f448513          	addi	a0,s1,1012
40005e6a:	3ef4a823          	sw	a5,1008(s1)
40005e6e:	14d520ef          	jal	400587ba <memcpy>
40005e72:	10842783          	lw	a5,264(s0)
40005e76:	40f4ac23          	sw	a5,1048(s1)
40005e7a:	10c42783          	lw	a5,268(s0)
40005e7e:	40f4ae23          	sw	a5,1052(s1)
40005e82:	4791                	li	a5,4
40005e84:	14f40223          	sb	a5,324(s0)
40005e88:	15241123          	sh	s2,322(s0)
40005e8c:	b51d                	j	40005cb2 <r_ecc_point_multiplication_win_256+0x1f6>
40005e8e:	4711                	li	a4,4
40005e90:	e2e911e3          	bne	s2,a4,40005cb2 <r_ecc_point_multiplication_win_256+0x1f6>
40005e94:	02f59163          	bne	a1,a5,40005eb6 <r_ecc_point_multiplication_win_256+0x3fa>
40005e98:	3fce07b7          	lui	a5,0x3fce0
40005e9c:	f887a783          	lw	a5,-120(a5) # 3fcdff88 <r_modules_funcs_p>
40005ea0:	14852503          	lw	a0,328(a0)
40005ea4:	3887a783          	lw	a5,904(a5)
40005ea8:	10850613          	addi	a2,a0,264
40005eac:	08450593          	addi	a1,a0,132
40005eb0:	9782                	jalr	a5
40005eb2:	4795                	li	a5,5
40005eb4:	b3ed                	j	40005c9e <r_ecc_point_multiplication_win_256+0x1e2>
40005eb6:	4795                	li	a5,5
40005eb8:	02f59163          	bne	a1,a5,40005eda <r_ecc_point_multiplication_win_256+0x41e>
40005ebc:	3fce07b7          	lui	a5,0x3fce0
40005ec0:	f887a783          	lw	a5,-120(a5) # 3fcdff88 <r_modules_funcs_p>
40005ec4:	14852503          	lw	a0,328(a0)
40005ec8:	3887a783          	lw	a5,904(a5)
40005ecc:	21050613          	addi	a2,a0,528
40005ed0:	18c50593          	addi	a1,a0,396
40005ed4:	9782                	jalr	a5
40005ed6:	4799                	li	a5,6
40005ed8:	b3d9                	j	40005c9e <r_ecc_point_multiplication_win_256+0x1e2>
40005eda:	4719                	li	a4,6
40005edc:	02e59363          	bne	a1,a4,40005f02 <r_ecc_point_multiplication_win_256+0x446>
40005ee0:	3fce07b7          	lui	a5,0x3fce0
40005ee4:	f887a783          	lw	a5,-120(a5) # 3fcdff88 <r_modules_funcs_p>
40005ee8:	14852503          	lw	a0,328(a0)
40005eec:	3887a783          	lw	a5,904(a5)
40005ef0:	29450613          	addi	a2,a0,660
40005ef4:	18c50593          	addi	a1,a0,396
40005ef8:	08450513          	addi	a0,a0,132
40005efc:	9782                	jalr	a5
40005efe:	479d                	li	a5,7
40005f00:	bb79                	j	40005c9e <r_ecc_point_multiplication_win_256+0x1e2>
40005f02:	479d                	li	a5,7
40005f04:	02f59163          	bne	a1,a5,40005f26 <r_ecc_point_multiplication_win_256+0x46a>
40005f08:	3fce07b7          	lui	a5,0x3fce0
40005f0c:	f887a783          	lw	a5,-120(a5) # 3fcdff88 <r_modules_funcs_p>
40005f10:	14852503          	lw	a0,328(a0)
40005f14:	3887a783          	lw	a5,904(a5)
40005f18:	31850613          	addi	a2,a0,792
40005f1c:	29450593          	addi	a1,a0,660
40005f20:	9782                	jalr	a5
40005f22:	47a5                	li	a5,9
40005f24:	bbad                	j	40005c9e <r_ecc_point_multiplication_win_256+0x1e2>
40005f26:	ff758793          	addi	a5,a1,-9
40005f2a:	07c2                	slli	a5,a5,0x10
40005f2c:	83c1                	srli	a5,a5,0x10
40005f2e:	d8f762e3          	bltu	a4,a5,40005cb2 <r_ecc_point_multiplication_win_256+0x1f6>
40005f32:	08400793          	li	a5,132
40005f36:	02f585b3          	mul	a1,a1,a5
40005f3a:	3fce07b7          	lui	a5,0x3fce0
40005f3e:	f887a783          	lw	a5,-120(a5) # 3fcdff88 <r_modules_funcs_p>
40005f42:	14852503          	lw	a0,328(a0)
40005f46:	3887a783          	lw	a5,904(a5)
40005f4a:	f7c58613          	addi	a2,a1,-132
40005f4e:	b5c58593          	addi	a1,a1,-1188
40005f52:	962a                	add	a2,a2,a0
40005f54:	95aa                	add	a1,a1,a0
40005f56:	39c50513          	addi	a0,a0,924
40005f5a:	9782                	jalr	a5
40005f5c:	14245783          	lhu	a5,322(s0)
40005f60:	473d                	li	a4,15
40005f62:	00e79863          	bne	a5,a4,40005f72 <r_ecc_point_multiplication_win_256+0x4b6>
40005f66:	4789                	li	a5,2
40005f68:	14f40223          	sb	a5,324(s0)
40005f6c:	03f00793          	li	a5,63
40005f70:	b33d                	j	40005c9e <r_ecc_point_multiplication_win_256+0x1e2>
40005f72:	0785                	addi	a5,a5,1
40005f74:	b32d                	j	40005c9e <r_ecc_point_multiplication_win_256+0x1e2>
