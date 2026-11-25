
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .text:

400487f4 <ets_emsa_pss_verify>:
400487f4:	7111                	addi	sp,sp,-256
400487f6:	dda2                	sw	s0,248(sp)
400487f8:	df86                	sw	ra,252(sp)
400487fa:	dba6                	sw	s1,244(sp)
400487fc:	d9ca                	sw	s2,240(sp)
400487fe:	d7ce                	sw	s3,236(sp)
40048800:	d5d2                	sw	s4,232(sp)
40048802:	d3d6                	sw	s5,228(sp)
40048804:	d1da                	sw	s6,224(sp)
40048806:	0200                	addi	s0,sp,256
40048808:	17f54703          	lbu	a4,383(a0)
4004880c:	0bc00793          	li	a5,188
40048810:	710d                	addi	sp,sp,-352
40048812:	02f70463          	beq	a4,a5,4004883a <ets_emsa_pss_verify+0x46>
40048816:	3ff1c537          	lui	a0,0x3ff1c
4004881a:	b5850513          	addi	a0,a0,-1192 # 3ff1bb58 <usb_data_stuff+0x40>
4004881e:	3d5d                	jal	400486d4 <ets_printf>
40048820:	4501                	li	a0,0
40048822:	f0040113          	addi	sp,s0,-256
40048826:	50fe                	lw	ra,252(sp)
40048828:	546e                	lw	s0,248(sp)
4004882a:	54de                	lw	s1,244(sp)
4004882c:	594e                	lw	s2,240(sp)
4004882e:	59be                	lw	s3,236(sp)
40048830:	5a2e                	lw	s4,232(sp)
40048832:	5a9e                	lw	s5,228(sp)
40048834:	5b0e                	lw	s6,224(sp)
40048836:	6111                	addi	sp,sp,256
40048838:	8082                	ret
4004883a:	00054903          	lbu	s2,0(a0)
4004883e:	89aa                	mv	s3,a0
40048840:	40795913          	srai	s2,s2,0x7
40048844:	fc0919e3          	bnez	s2,40048816 <ets_emsa_pss_verify+0x22>
40048848:	15f50a13          	addi	s4,a0,351
4004884c:	8aae                	mv	s5,a1
4004884e:	8b32                	mv	s6,a2
40048850:	868a                	mv	a3,sp
40048852:	15f00613          	li	a2,351
40048856:	02000593          	li	a1,32
4004885a:	8552                	mv	a0,s4
4004885c:	3dc5                	jal	4004874c <ets_mgf1_sha256>
4004885e:	848a                	mv	s1,sp
40048860:	4781                	li	a5,0
40048862:	15f00613          	li	a2,351
40048866:	00f486b3          	add	a3,s1,a5
4004886a:	00f98733          	add	a4,s3,a5
4004886e:	0006c583          	lbu	a1,0(a3)
40048872:	00074703          	lbu	a4,0(a4)
40048876:	0785                	addi	a5,a5,1
40048878:	8f2d                	xor	a4,a4,a1
4004887a:	00e68023          	sb	a4,0(a3)
4004887e:	fec794e3          	bne	a5,a2,40048866 <ets_emsa_pss_verify+0x72>
40048882:	0004c783          	lbu	a5,0(s1)
40048886:	13e00713          	li	a4,318
4004888a:	07f7f793          	andi	a5,a5,127
4004888e:	00f48023          	sb	a5,0(s1)
40048892:	4781                	li	a5,0
40048894:	00f486b3          	add	a3,s1,a5
40048898:	0006c683          	lbu	a3,0(a3)
4004889c:	fead                	bnez	a3,40048816 <ets_emsa_pss_verify+0x22>
4004889e:	0785                	addi	a5,a5,1
400488a0:	fee79ae3          	bne	a5,a4,40048894 <ets_emsa_pss_verify+0xa0>
400488a4:	13e4c703          	lbu	a4,318(s1)
400488a8:	4785                	li	a5,1
400488aa:	f6f716e3          	bne	a4,a5,40048816 <ets_emsa_pss_verify+0x22>
400488ae:	02000613          	li	a2,32
400488b2:	13f48593          	addi	a1,s1,319
400488b6:	02848513          	addi	a0,s1,40
400488ba:	7010f0ef          	jal	400587ba <memcpy>
400488be:	4621                	li	a2,8
400488c0:	4581                	li	a1,0
400488c2:	8526                	mv	a0,s1
400488c4:	01a100ef          	jal	400588de <memset>
400488c8:	02000613          	li	a2,32
400488cc:	85d6                	mv	a1,s5
400488ce:	00848513          	addi	a0,s1,8
400488d2:	6e90f0ef          	jal	400587ba <memcpy>
400488d6:	407000ef          	jal	400494dc <ets_sha_enable>
400488da:	4589                	li	a1,2
400488dc:	f0840513          	addi	a0,s0,-248
400488e0:	427000ef          	jal	40049506 <ets_sha_init>
400488e4:	4681                	li	a3,0
400488e6:	04800613          	li	a2,72
400488ea:	85a6                	mv	a1,s1
400488ec:	f0840513          	addi	a0,s0,-248
400488f0:	557000ef          	jal	40049646 <ets_sha_update>
400488f4:	85a6                	mv	a1,s1
400488f6:	f0840513          	addi	a0,s0,-248
400488fa:	65d000ef          	jal	40049756 <ets_sha_finish>
400488fe:	3f5000ef          	jal	400494f2 <ets_sha_disable>
40048902:	02000713          	li	a4,32
40048906:	012987b3          	add	a5,s3,s2
4004890a:	012a8633          	add	a2,s5,s2
4004890e:	00064603          	lbu	a2,0(a2)
40048912:	15f7c783          	lbu	a5,351(a5)
40048916:	012b06b3          	add	a3,s6,s2
4004891a:	8fb1                	xor	a5,a5,a2
4004891c:	01248633          	add	a2,s1,s2
40048920:	00064603          	lbu	a2,0(a2)
40048924:	0905                	addi	s2,s2,1
40048926:	8fb1                	xor	a5,a5,a2
40048928:	00f68023          	sb	a5,0(a3)
4004892c:	fce91de3          	bne	s2,a4,40048906 <ets_emsa_pss_verify+0x112>
40048930:	02000613          	li	a2,32
40048934:	85a6                	mv	a1,s1
40048936:	8552                	mv	a0,s4
40048938:	63b0f0ef          	jal	40058772 <memcmp>
4004893c:	ec051de3          	bnez	a0,40048816 <ets_emsa_pss_verify+0x22>
40048940:	4505                	li	a0,1
40048942:	b5c5                	j	40048822 <ets_emsa_pss_verify+0x2e>
