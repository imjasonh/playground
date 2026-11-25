
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

40035784 <tdefl_compress>:
40035784:	e911                	bnez	a0,40035798 <tdefl_compress+0x14>
40035786:	c219                	beqz	a2,4003578c <tdefl_compress+0x8>
40035788:	00062023          	sw	zero,0(a2)
4003578c:	5579                	li	a0,-2
4003578e:	7e070963          	beqz	a4,40035f80 <tdefl_compress+0x7fc>
40035792:	00072023          	sw	zero,0(a4)
40035796:	8082                	ret
40035798:	715d                	addi	sp,sp,-80
4003579a:	c2a6                	sw	s1,68(sp)
4003579c:	c686                	sw	ra,76(sp)
4003579e:	c4a2                	sw	s0,72(sp)
400357a0:	c0ca                	sw	s2,64(sp)
400357a2:	de4e                	sw	s3,60(sp)
400357a4:	dc52                	sw	s4,56(sp)
400357a6:	da56                	sw	s5,52(sp)
400357a8:	d85a                	sw	s6,48(sp)
400357aa:	d65e                	sw	s7,44(sp)
400357ac:	d462                	sw	s8,40(sp)
400357ae:	d266                	sw	s9,36(sp)
400357b0:	d06a                	sw	s10,32(sp)
400357b2:	ce6e                	sw	s11,28(sp)
400357b4:	d92c                	sw	a1,112(a0)
400357b6:	dd30                	sw	a2,120(a0)
400357b8:	d974                	sw	a3,116(a0)
400357ba:	dd78                	sw	a4,124(a0)
400357bc:	08b52223          	sw	a1,132(a0)
400357c0:	4481                	li	s1,0
400357c2:	c211                	beqz	a2,400357c6 <tdefl_compress+0x42>
400357c4:	4204                	lw	s1,0(a2)
400357c6:	00052803          	lw	a6,0(a0)
400357ca:	08952423          	sw	s1,136(a0)
400357ce:	08052623          	sw	zero,140(a0)
400357d2:	08f52023          	sw	a5,128(a0)
400357d6:	00183813          	seqz	a6,a6
400357da:	4885                	li	a7,1
400357dc:	e299                	bnez	a3,400357e2 <tdefl_compress+0x5e>
400357de:	00e038b3          	snez	a7,a4
400357e2:	03181b63          	bne	a6,a7,40035818 <tdefl_compress+0x94>
400357e6:	06c52803          	lw	a6,108(a0)
400357ea:	02081763          	bnez	a6,40035818 <tdefl_compress+0x94>
400357ee:	06852803          	lw	a6,104(a0)
400357f2:	00080563          	beqz	a6,400357fc <tdefl_compress+0x78>
400357f6:	4891                	li	a7,4
400357f8:	03179063          	bne	a5,a7,40035818 <tdefl_compress+0x94>
400357fc:	c611                	beqz	a2,40035808 <tdefl_compress+0x84>
400357fe:	00062883          	lw	a7,0(a2)
40035802:	00088363          	beqz	a7,40035808 <tdefl_compress+0x84>
40035806:	c991                	beqz	a1,4003581a <tdefl_compress+0x96>
40035808:	c321                	beqz	a4,40035848 <tdefl_compress+0xc4>
4003580a:	00072883          	lw	a7,0(a4)
4003580e:	02088d63          	beqz	a7,40035848 <tdefl_compress+0xc4>
40035812:	ea9d                	bnez	a3,40035848 <tdefl_compress+0xc4>
40035814:	e219                	bnez	a2,4003581a <tdefl_compress+0x96>
40035816:	a029                	j	40035820 <tdefl_compress+0x9c>
40035818:	c219                	beqz	a2,4003581e <tdefl_compress+0x9a>
4003581a:	00062023          	sw	zero,0(a2)
4003581e:	c319                	beqz	a4,40035824 <tdefl_compress+0xa0>
40035820:	00072023          	sw	zero,0(a4)
40035824:	57f9                	li	a5,-2
40035826:	d57c                	sw	a5,108(a0)
40035828:	5579                	li	a0,-2
4003582a:	40b6                	lw	ra,76(sp)
4003582c:	4426                	lw	s0,72(sp)
4003582e:	4496                	lw	s1,68(sp)
40035830:	4906                	lw	s2,64(sp)
40035832:	59f2                	lw	s3,60(sp)
40035834:	5a62                	lw	s4,56(sp)
40035836:	5ad2                	lw	s5,52(sp)
40035838:	5b42                	lw	s6,48(sp)
4003583a:	5bb2                	lw	s7,44(sp)
4003583c:	5c22                	lw	s8,40(sp)
4003583e:	5c92                	lw	s9,36(sp)
40035840:	5d02                	lw	s10,32(sp)
40035842:	4df2                	lw	s11,28(sp)
40035844:	6161                	addi	sp,sp,80
40035846:	8082                	ret
40035848:	ffc78a13          	addi	s4,a5,-4
4003584c:	89be                	mv	s3,a5
4003584e:	001a3a13          	seqz	s4,s4
40035852:	4d7c                	lw	a5,92(a0)
40035854:	01486833          	or	a6,a6,s4
40035858:	07052423          	sw	a6,104(a0)
4003585c:	8aae                	mv	s5,a1
4003585e:	842a                	mv	s0,a0
40035860:	e781                	bnez	a5,40035868 <tdefl_compress+0xe4>
40035862:	513c                	lw	a5,96(a0)
40035864:	5e078863          	beqz	a5,40035e54 <tdefl_compress+0x6d0>
40035868:	8522                	mv	a0,s0
4003586a:	b2bfd0ef          	jal	40033394 <tdefl_flush_output_buffer>
4003586e:	d468                	sw	a0,108(s0)
40035870:	bf6d                	j	4003582a <tdefl_compress+0xa6>
40035872:	500c                	lw	a1,32(s0)
40035874:	5054                	lw	a3,36(s0)
40035876:	4785                	li	a5,1
40035878:	00d58733          	add	a4,a1,a3
4003587c:	08e7ef63          	bltu	a5,a4,4003591a <tdefl_compress+0x196>
40035880:	6509                	lui	a0,0x2
40035882:	6585                	lui	a1,0x1
40035884:	10100893          	li	a7,257
40035888:	fff50613          	addi	a2,a0,-1 # 1fff <RvExcFrameSize+0x1f6f>
4003588c:	10000313          	li	t1,256
40035890:	4e09                	li	t3,2
40035892:	15fd                	addi	a1,a1,-1 # fff <RvExcFrameSize+0xf6f>
40035894:	6ea5                	lui	t4,0x9
40035896:	938b8f13          	addi	t5,s7,-1736
4003589a:	501c                	lw	a5,32(s0)
4003589c:	c8f9                	beqz	s1,40035972 <tdefl_compress+0x1ee>
4003589e:	0cf8ea63          	bltu	a7,a5,40035972 <tdefl_compress+0x1ee>
400358a2:	01c42f83          	lw	t6,28(s0)
400358a6:	0905                	addi	s2,s2,1
400358a8:	fff94283          	lbu	t0,-1(s2)
400358ac:	00ff8833          	add	a6,t6,a5
400358b0:	00c87833          	and	a6,a6,a2
400358b4:	01040733          	add	a4,s0,a6
400358b8:	08570823          	sb	t0,144(a4)
400358bc:	14fd                	addi	s1,s1,-1
400358be:	01036563          	bltu	t1,a6,400358c8 <tdefl_compress+0x144>
400358c2:	972a                	add	a4,a4,a0
400358c4:	08570823          	sb	t0,144(a4)
400358c8:	0785                	addi	a5,a5,1
400358ca:	d01c                	sw	a5,32(s0)
400358cc:	00f68733          	add	a4,a3,a5
400358d0:	fcee75e3          	bgeu	t3,a4,4003589a <tdefl_compress+0x116>
400358d4:	9fbe                	add	t6,t6,a5
400358d6:	ffdf8813          	addi	a6,t6,-3
400358da:	1ff9                	addi	t6,t6,-2
400358dc:	00cfffb3          	and	t6,t6,a2
400358e0:	00c87733          	and	a4,a6,a2
400358e4:	9fa2                	add	t6,t6,s0
400358e6:	090fc783          	lbu	a5,144(t6)
400358ea:	00e40fb3          	add	t6,s0,a4
400358ee:	090fcf83          	lbu	t6,144(t6)
400358f2:	0792                	slli	a5,a5,0x4
400358f4:	977a                	add	a4,a4,t5
400358f6:	0fa2                	slli	t6,t6,0x8
400358f8:	01f7c7b3          	xor	a5,a5,t6
400358fc:	0057c7b3          	xor	a5,a5,t0
40035900:	8fed                	and	a5,a5,a1
40035902:	0786                	slli	a5,a5,0x1
40035904:	97a2                	add	a5,a5,s0
40035906:	97f6                	add	a5,a5,t4
40035908:	2727df83          	lhu	t6,626(a5)
4003590c:	0706                	slli	a4,a4,0x1
4003590e:	9722                	add	a4,a4,s0
40035910:	01f71123          	sh	t6,2(a4)
40035914:	27079923          	sh	a6,626(a5)
40035918:	b749                	j	4003589a <tdefl_compress+0x116>
4003591a:	4c58                	lw	a4,28(s0)
4003591c:	6809                	lui	a6,0x2
4003591e:	187d                	addi	a6,a6,-1 # 1fff <RvExcFrameSize+0x1f6f>
40035920:	972e                	add	a4,a4,a1
40035922:	ffe70513          	addi	a0,a4,-2
40035926:	01077633          	and	a2,a4,a6
4003592a:	010577b3          	and	a5,a0,a6
4003592e:	177d                	addi	a4,a4,-1
40035930:	97a2                	add	a5,a5,s0
40035932:	01077733          	and	a4,a4,a6
40035936:	0907c783          	lbu	a5,144(a5)
4003593a:	9722                	add	a4,a4,s0
4003593c:	09074703          	lbu	a4,144(a4)
40035940:	0792                	slli	a5,a5,0x4
40035942:	8fb9                	xor	a5,a5,a4
40035944:	10200713          	li	a4,258
40035948:	8f0d                	sub	a4,a4,a1
4003594a:	00e4f363          	bgeu	s1,a4,40035950 <tdefl_compress+0x1cc>
4003594e:	8726                	mv	a4,s1
40035950:	00e90e33          	add	t3,s2,a4
40035954:	8c99                	sub	s1,s1,a4
40035956:	6889                	lui	a7,0x2
40035958:	972e                	add	a4,a4,a1
4003595a:	6805                	lui	a6,0x1
4003595c:	d018                	sw	a4,32(s0)
4003595e:	10000e93          	li	t4,256
40035962:	187d                	addi	a6,a6,-1 # fff <RvExcFrameSize+0xf6f>
40035964:	6f25                	lui	t5,0x9
40035966:	fff88313          	addi	t1,a7,-1 # 1fff <RvExcFrameSize+0x1f6f>
4003596a:	938b8f93          	addi	t6,s7,-1736
4003596e:	072e1d63          	bne	t3,s2,400359e8 <tdefl_compress+0x264>
40035972:	500c                	lw	a1,32(s0)
40035974:	6889                	lui	a7,0x2
40035976:	40b888b3          	sub	a7,a7,a1
4003597a:	0116f363          	bgeu	a3,a7,40035980 <tdefl_compress+0x1fc>
4003597e:	88b6                	mv	a7,a3
40035980:	03142223          	sw	a7,36(s0)
40035984:	00099663          	bnez	s3,40035990 <tdefl_compress+0x20c>
40035988:	10100793          	li	a5,257
4003598c:	4eb7fa63          	bgeu	a5,a1,40035e80 <tdefl_compress+0x6fc>
40035990:	483c                	lw	a5,80(s0)
40035992:	4689                	li	a3,2
40035994:	c391                	beqz	a5,40035998 <tdefl_compress+0x214>
40035996:	86be                	mv	a3,a5
40035998:	00842f83          	lw	t6,8(s0)
4003599c:	01c42e83          	lw	t4,28(s0)
400359a0:	6309                	lui	t1,0x2
400359a2:	00090737          	lui	a4,0x90
400359a6:	137d                	addi	t1,t1,-1 # 1fff <RvExcFrameSize+0x1f6f>
400359a8:	00eff733          	and	a4,t6,a4
400359ac:	006ef533          	and	a0,t4,t1
400359b0:	c759                	beqz	a4,40035a3e <tdefl_compress+0x2ba>
400359b2:	5a088b63          	beqz	a7,40035f68 <tdefl_compress+0x7e4>
400359b6:	00080637          	lui	a2,0x80
400359ba:	00cff633          	and	a2,t6,a2
400359be:	4881                	li	a7,0
400359c0:	5a061463          	bnez	a2,40035f68 <tdefl_compress+0x7e4>
400359c4:	fff50713          	addi	a4,a0,-1
400359c8:	00677333          	and	t1,a4,t1
400359cc:	9322                	add	t1,t1,s0
400359ce:	09034803          	lbu	a6,144(t1)
400359d2:	00a40733          	add	a4,s0,a0
400359d6:	4681                	li	a3,0
400359d8:	04d59c63          	bne	a1,a3,40035a30 <tdefl_compress+0x2ac>
400359dc:	4709                	li	a4,2
400359de:	4885                	li	a7,1
400359e0:	58d76463          	bltu	a4,a3,40035f68 <tdefl_compress+0x7e4>
400359e4:	4681                	li	a3,0
400359e6:	a2b1                	j	40035b32 <tdefl_compress+0x3ae>
400359e8:	0905                	addi	s2,s2,1
400359ea:	fff94583          	lbu	a1,-1(s2)
400359ee:	00c40733          	add	a4,s0,a2
400359f2:	08b70823          	sb	a1,144(a4) # 90090 <RvExcFrameSize+0x90000>
400359f6:	00cee563          	bltu	t4,a2,40035a00 <tdefl_compress+0x27c>
400359fa:	9746                	add	a4,a4,a7
400359fc:	08b70823          	sb	a1,144(a4)
40035a00:	0792                	slli	a5,a5,0x4
40035a02:	8fad                	xor	a5,a5,a1
40035a04:	0107f7b3          	and	a5,a5,a6
40035a08:	00179593          	slli	a1,a5,0x1
40035a0c:	95a2                	add	a1,a1,s0
40035a0e:	95fa                	add	a1,a1,t5
40035a10:	00657733          	and	a4,a0,t1
40035a14:	2725d283          	lhu	t0,626(a1)
40035a18:	977e                	add	a4,a4,t6
40035a1a:	0706                	slli	a4,a4,0x1
40035a1c:	9722                	add	a4,a4,s0
40035a1e:	00571123          	sh	t0,2(a4)
40035a22:	0605                	addi	a2,a2,1 # 80001 <RvExcFrameSize+0x7ff71>
40035a24:	26a59923          	sh	a0,626(a1)
40035a28:	00667633          	and	a2,a2,t1
40035a2c:	0505                	addi	a0,a0,1
40035a2e:	b781                	j	4003596e <tdefl_compress+0x1ea>
40035a30:	0705                	addi	a4,a4,1
40035a32:	08f74883          	lbu	a7,143(a4)
40035a36:	fb0893e3          	bne	a7,a6,400359dc <tdefl_compress+0x258>
40035a3a:	0685                	addi	a3,a3,1
40035a3c:	bf71                	j	400359d8 <tdefl_compress+0x254>
40035a3e:	52b6f463          	bgeu	a3,a1,40035f66 <tdefl_compress+0x7e2>
40035a42:	0206b713          	sltiu	a4,a3,32
40035a46:	00174713          	xori	a4,a4,1
40035a4a:	070a                	slli	a4,a4,0x2
40035a4c:	9722                	add	a4,a4,s0
40035a4e:	00c72083          	lw	ra,12(a4)
40035a52:	00d50733          	add	a4,a0,a3
40035a56:	9722                	add	a4,a4,s0
40035a58:	0ec2                	slli	t4,t4,0x10
40035a5a:	09074283          	lbu	t0,144(a4)
40035a5e:	08f74383          	lbu	t2,143(a4)
40035a62:	09040d13          	addi	s10,s0,144
40035a66:	4601                	li	a2,0
40035a68:	872a                	mv	a4,a0
40035a6a:	938b8c13          	addi	s8,s7,-1736
40035a6e:	010ede93          	srli	t4,t4,0x10
40035a72:	10fd                	addi	ra,ra,-1
40035a74:	0a008963          	beqz	ra,40035b26 <tdefl_compress+0x3a2>
40035a78:	9762                	add	a4,a4,s8
40035a7a:	0706                	slli	a4,a4,0x1
40035a7c:	9722                	add	a4,a4,s0
40035a7e:	00275703          	lhu	a4,2(a4)
40035a82:	c355                	beqz	a4,40035b26 <tdefl_compress+0x3a2>
40035a84:	40ee8833          	sub	a6,t4,a4
40035a88:	0842                	slli	a6,a6,0x10
40035a8a:	01085813          	srli	a6,a6,0x10
40035a8e:	0908ec63          	bltu	a7,a6,40035b26 <tdefl_compress+0x3a2>
40035a92:	00677733          	and	a4,a4,t1
40035a96:	00d70e33          	add	t3,a4,a3
40035a9a:	9e22                	add	t3,t3,s0
40035a9c:	090e4f03          	lbu	t5,144(t3)
40035aa0:	005f1663          	bne	t5,t0,40035aac <tdefl_compress+0x328>
40035aa4:	08fe4e03          	lbu	t3,143(t3)
40035aa8:	067e0663          	beq	t3,t2,40035b14 <tdefl_compress+0x390>
40035aac:	9762                	add	a4,a4,s8
40035aae:	0706                	slli	a4,a4,0x1
40035ab0:	9722                	add	a4,a4,s0
40035ab2:	00275703          	lhu	a4,2(a4)
40035ab6:	cb25                	beqz	a4,40035b26 <tdefl_compress+0x3a2>
40035ab8:	40ee8833          	sub	a6,t4,a4
40035abc:	0842                	slli	a6,a6,0x10
40035abe:	01085813          	srli	a6,a6,0x10
40035ac2:	0708e263          	bltu	a7,a6,40035b26 <tdefl_compress+0x3a2>
40035ac6:	00677733          	and	a4,a4,t1
40035aca:	00e68e33          	add	t3,a3,a4
40035ace:	9e22                	add	t3,t3,s0
40035ad0:	090e4f03          	lbu	t5,144(t3)
40035ad4:	005f1663          	bne	t5,t0,40035ae0 <tdefl_compress+0x35c>
40035ad8:	08fe4e03          	lbu	t3,143(t3)
40035adc:	027e0c63          	beq	t3,t2,40035b14 <tdefl_compress+0x390>
40035ae0:	9762                	add	a4,a4,s8
40035ae2:	0706                	slli	a4,a4,0x1
40035ae4:	9722                	add	a4,a4,s0
40035ae6:	00275703          	lhu	a4,2(a4)
40035aea:	cf15                	beqz	a4,40035b26 <tdefl_compress+0x3a2>
40035aec:	40ee8833          	sub	a6,t4,a4
40035af0:	0842                	slli	a6,a6,0x10
40035af2:	01085813          	srli	a6,a6,0x10
40035af6:	0308e863          	bltu	a7,a6,40035b26 <tdefl_compress+0x3a2>
40035afa:	00677733          	and	a4,a4,t1
40035afe:	00e68e33          	add	t3,a3,a4
40035b02:	9e22                	add	t3,t3,s0
40035b04:	090e4f03          	lbu	t5,144(t3)
40035b08:	f65f15e3          	bne	t5,t0,40035a72 <tdefl_compress+0x2ee>
40035b0c:	08fe4e03          	lbu	t3,143(t3)
40035b10:	f67e11e3          	bne	t3,t2,40035a72 <tdefl_compress+0x2ee>
40035b14:	00080963          	beqz	a6,40035b26 <tdefl_compress+0x3a2>
40035b18:	4e01                	li	t3,0
40035b1a:	1dc59163          	bne	a1,t3,40035cdc <tdefl_compress+0x558>
40035b1e:	f4b6fae3          	bgeu	a3,a1,40035a72 <tdefl_compress+0x2ee>
40035b22:	86ae                	mv	a3,a1
40035b24:	8642                	mv	a2,a6
40035b26:	470d                	li	a4,3
40035b28:	00e69563          	bne	a3,a4,40035b32 <tdefl_compress+0x3ae>
40035b2c:	6709                	lui	a4,0x2
40035b2e:	38e67663          	bgeu	a2,a4,40035eba <tdefl_compress+0x736>
40035b32:	38c50463          	beq	a0,a2,40035eba <tdefl_compress+0x736>
40035b36:	00ef9713          	slli	a4,t6,0xe
40035b3a:	00075563          	bgez	a4,40035b44 <tdefl_compress+0x3c0>
40035b3e:	4715                	li	a4,5
40035b40:	36d77d63          	bgeu	a4,a3,40035eba <tdefl_compress+0x736>
40035b44:	540c                	lw	a1,40(s0)
40035b46:	1e078263          	beqz	a5,40035d2a <tdefl_compress+0x5a6>
40035b4a:	5c58                	lw	a4,60(s0)
40035b4c:	36d7f963          	bgeu	a5,a3,40035ebe <tdefl_compress+0x73a>
40035b50:	487c                	lw	a5,84(s0)
40035b52:	0705                	addi	a4,a4,1 # 2001 <RvExcFrameSize+0x1f71>
40035b54:	dc58                	sw	a4,60(s0)
40035b56:	00158713          	addi	a4,a1,1
40035b5a:	d418                	sw	a4,40(s0)
40035b5c:	00f58023          	sb	a5,0(a1)
40035b60:	544c                	lw	a1,44(s0)
40035b62:	0005c703          	lbu	a4,0(a1)
40035b66:	8305                	srli	a4,a4,0x1
40035b68:	00e58023          	sb	a4,0(a1)
40035b6c:	5c18                	lw	a4,56(s0)
40035b6e:	177d                	addi	a4,a4,-1
40035b70:	18070563          	beqz	a4,40035cfa <tdefl_compress+0x576>
40035b74:	dc18                	sw	a4,56(s0)
40035b76:	0ff7f793          	zext.b	a5,a5
40035b7a:	0786                	slli	a5,a5,0x1
40035b7c:	6709                	lui	a4,0x2
40035b7e:	97a2                	add	a5,a5,s0
40035b80:	97ba                	add	a5,a5,a4
40035b82:	1927d703          	lhu	a4,402(a5)
40035b86:	0705                	addi	a4,a4,1 # 2001 <RvExcFrameSize+0x1f71>
40035b88:	18e79923          	sh	a4,402(a5)
40035b8c:	07f00793          	li	a5,127
40035b90:	2ad7fb63          	bgeu	a5,a3,40035e46 <tdefl_compress+0x6c2>
40035b94:	5c5c                	lw	a5,60(s0)
40035b96:	540c                	lw	a1,40(s0)
40035b98:	ffd68713          	addi	a4,a3,-3
40035b9c:	97b6                	add	a5,a5,a3
40035b9e:	dc5c                	sw	a5,60(s0)
40035ba0:	00e58023          	sb	a4,0(a1)
40035ba4:	541c                	lw	a5,40(s0)
40035ba6:	167d                	addi	a2,a2,-1
40035ba8:	00865593          	srli	a1,a2,0x8
40035bac:	00c780a3          	sb	a2,1(a5)
40035bb0:	541c                	lw	a5,40(s0)
40035bb2:	00b78123          	sb	a1,2(a5)
40035bb6:	541c                	lw	a5,40(s0)
40035bb8:	5448                	lw	a0,44(s0)
40035bba:	078d                	addi	a5,a5,3
40035bbc:	d41c                	sw	a5,40(s0)
40035bbe:	00054783          	lbu	a5,0(a0)
40035bc2:	8385                	srli	a5,a5,0x1
40035bc4:	f807e793          	ori	a5,a5,-128
40035bc8:	00f50023          	sb	a5,0(a0)
40035bcc:	5c1c                	lw	a5,56(s0)
40035bce:	17fd                	addi	a5,a5,-1
40035bd0:	12078d63          	beqz	a5,40035d0a <tdefl_compress+0x586>
40035bd4:	dc1c                	sw	a5,56(s0)
40035bd6:	07f5f513          	andi	a0,a1,127
40035bda:	3ff1d5b7          	lui	a1,0x3ff1d
40035bde:	1ff67793          	andi	a5,a2,511
40035be2:	3bc58593          	addi	a1,a1,956 # 3ff1d3bc <s_tdefl_large_dist_sym>
40035be6:	95aa                	add	a1,a1,a0
40035be8:	97da                	add	a5,a5,s6
40035bea:	1ff00513          	li	a0,511
40035bee:	0007c783          	lbu	a5,0(a5)
40035bf2:	0005c583          	lbu	a1,0(a1)
40035bf6:	00c57363          	bgeu	a0,a2,40035bfc <tdefl_compress+0x478>
40035bfa:	87ae                	mv	a5,a1
40035bfc:	0786                	slli	a5,a5,0x1
40035bfe:	6589                	lui	a1,0x2
40035c00:	97a2                	add	a5,a5,s0
40035c02:	97ae                	add	a5,a5,a1
40035c04:	3d27d603          	lhu	a2,978(a5)
40035c08:	0605                	addi	a2,a2,1
40035c0a:	3cc79923          	sh	a2,978(a5)
40035c0e:	00171613          	slli	a2,a4,0x1
40035c12:	3ff1d737          	lui	a4,0x3ff1d
40035c16:	53c70713          	addi	a4,a4,1340 # 3ff1d53c <s_tdefl_len_sym>
40035c1a:	9732                	add	a4,a4,a2
40035c1c:	00075783          	lhu	a5,0(a4)
40035c20:	0786                	slli	a5,a5,0x1
40035c22:	97a2                	add	a5,a5,s0
40035c24:	97ae                	add	a5,a5,a1
40035c26:	1927d703          	lhu	a4,402(a5)
40035c2a:	0705                	addi	a4,a4,1
40035c2c:	18e79923          	sh	a4,402(a5)
40035c30:	04042823          	sw	zero,80(s0)
40035c34:	4c5c                	lw	a5,28(s0)
40035c36:	97b6                	add	a5,a5,a3
40035c38:	cc5c                	sw	a5,28(s0)
40035c3a:	501c                	lw	a5,32(s0)
40035c3c:	8f95                	sub	a5,a5,a3
40035c3e:	d01c                	sw	a5,32(s0)
40035c40:	505c                	lw	a5,36(s0)
40035c42:	96be                	add	a3,a3,a5
40035c44:	6789                	lui	a5,0x2
40035c46:	00d7f363          	bgeu	a5,a3,40035c4c <tdefl_compress+0x4c8>
40035c4a:	6689                	lui	a3,0x2
40035c4c:	541c                	lw	a5,40(s0)
40035c4e:	4722                	lw	a4,8(sp)
40035c50:	d054                	sw	a3,36(s0)
40035c52:	02f76663          	bltu	a4,a5,40035c7e <tdefl_compress+0x4fa>
40035c56:	5c54                	lw	a3,60(s0)
40035c58:	6721                	lui	a4,0x8
40035c5a:	c0070713          	addi	a4,a4,-1024 # 7c00 <RvExcFrameSize+0x7b70>
40035c5e:	20d77a63          	bgeu	a4,a3,40035e72 <tdefl_compress+0x6ee>
40035c62:	4732                	lw	a4,12(sp)
40035c64:	8f99                	sub	a5,a5,a4
40035c66:	07300713          	li	a4,115
40035c6a:	02e787b3          	mul	a5,a5,a4
40035c6e:	839d                	srli	a5,a5,0x7
40035c70:	00d7f763          	bgeu	a5,a3,40035c7e <tdefl_compress+0x4fa>
40035c74:	441c                	lw	a5,8(s0)
40035c76:	00c79713          	slli	a4,a5,0xc
40035c7a:	1e075c63          	bgez	a4,40035e72 <tdefl_compress+0x6ee>
40035c7e:	09242223          	sw	s2,132(s0)
40035c82:	08942423          	sw	s1,136(s0)
40035c86:	4581                	li	a1,0
40035c88:	8522                	mv	a0,s0
40035c8a:	b84fe0ef          	jal	4003400e <tdefl_flush_block>
40035c8e:	1e050263          	beqz	a0,40035e72 <tdefl_compress+0x6ee>
40035c92:	04054363          	bltz	a0,40035cd8 <tdefl_compress+0x554>
40035c96:	4418                	lw	a4,8(s0)
40035c98:	678d                	lui	a5,0x3
40035c9a:	8ff9                	and	a5,a5,a4
40035c9c:	cf81                	beqz	a5,40035cb4 <tdefl_compress+0x530>
40035c9e:	000a8b63          	beqz	s5,40035cb4 <tdefl_compress+0x530>
40035ca2:	08442603          	lw	a2,132(s0)
40035ca6:	4c08                	lw	a0,24(s0)
40035ca8:	85d6                	mv	a1,s5
40035caa:	41560633          	sub	a2,a2,s5
40035cae:	843fe0ef          	jal	400344f0 <mz_adler32>
40035cb2:	cc08                	sw	a0,24(s0)
40035cb4:	ba098ae3          	beqz	s3,40035868 <tdefl_compress+0xe4>
40035cb8:	501c                	lw	a5,32(s0)
40035cba:	ba0797e3          	bnez	a5,40035868 <tdefl_compress+0xe4>
40035cbe:	08842783          	lw	a5,136(s0)
40035cc2:	ba0793e3          	bnez	a5,40035868 <tdefl_compress+0xe4>
40035cc6:	4c7c                	lw	a5,92(s0)
40035cc8:	ba0790e3          	bnez	a5,40035868 <tdefl_compress+0xe4>
40035ccc:	85ce                	mv	a1,s3
40035cce:	8522                	mv	a0,s0
40035cd0:	b3efe0ef          	jal	4003400e <tdefl_flush_block>
40035cd4:	1a055b63          	bgez	a0,40035e8a <tdefl_compress+0x706>
40035cd8:	5468                	lw	a0,108(s0)
40035cda:	be81                	j	4003582a <tdefl_compress+0xa6>
40035cdc:	01c50f33          	add	t5,a0,t3
40035ce0:	01c70cb3          	add	s9,a4,t3
40035ce4:	01ed0db3          	add	s11,s10,t5
40035ce8:	9cea                	add	s9,s9,s10
40035cea:	000dcd83          	lbu	s11,0(s11)
40035cee:	000ccc83          	lbu	s9,0(s9)
40035cf2:	279d9d63          	bne	s11,s9,40035f6c <tdefl_compress+0x7e8>
40035cf6:	0e05                	addi	t3,t3,1
40035cf8:	b50d                	j	40035b1a <tdefl_compress+0x396>
40035cfa:	4721                	li	a4,8
40035cfc:	dc18                	sw	a4,56(s0)
40035cfe:	5418                	lw	a4,40(s0)
40035d00:	00170593          	addi	a1,a4,1
40035d04:	d40c                	sw	a1,40(s0)
40035d06:	d458                	sw	a4,44(s0)
40035d08:	b5bd                	j	40035b76 <tdefl_compress+0x3f2>
40035d0a:	47a1                	li	a5,8
40035d0c:	dc1c                	sw	a5,56(s0)
40035d0e:	541c                	lw	a5,40(s0)
40035d10:	00178513          	addi	a0,a5,1 # 3001 <RvExcFrameSize+0x2f71>
40035d14:	d408                	sw	a0,40(s0)
40035d16:	d45c                	sw	a5,44(s0)
40035d18:	bd7d                	j	40035bd6 <tdefl_compress+0x452>
40035d1a:	4721                	li	a4,8
40035d1c:	dc18                	sw	a4,56(s0)
40035d1e:	5418                	lw	a4,40(s0)
40035d20:	00170593          	addi	a1,a4,1
40035d24:	d40c                	sw	a1,40(s0)
40035d26:	d458                	sw	a4,44(s0)
40035d28:	aae9                	j	40035f02 <tdefl_compress+0x77e>
40035d2a:	ea31                	bnez	a2,40035d7e <tdefl_compress+0x5fa>
40035d2c:	5c58                	lw	a4,60(s0)
40035d2e:	9522                	add	a0,a0,s0
40035d30:	09054783          	lbu	a5,144(a0)
40035d34:	0705                	addi	a4,a4,1
40035d36:	dc58                	sw	a4,60(s0)
40035d38:	5418                	lw	a4,40(s0)
40035d3a:	00170693          	addi	a3,a4,1
40035d3e:	d414                	sw	a3,40(s0)
40035d40:	00f70023          	sb	a5,0(a4)
40035d44:	5454                	lw	a3,44(s0)
40035d46:	0006c703          	lbu	a4,0(a3) # 2000 <RvExcFrameSize+0x1f70>
40035d4a:	8305                	srli	a4,a4,0x1
40035d4c:	00e68023          	sb	a4,0(a3)
40035d50:	5c18                	lw	a4,56(s0)
40035d52:	177d                	addi	a4,a4,-1
40035d54:	cf09                	beqz	a4,40035d6e <tdefl_compress+0x5ea>
40035d56:	dc18                	sw	a4,56(s0)
40035d58:	0786                	slli	a5,a5,0x1
40035d5a:	6709                	lui	a4,0x2
40035d5c:	97a2                	add	a5,a5,s0
40035d5e:	97ba                	add	a5,a5,a4
40035d60:	1927d703          	lhu	a4,402(a5)
40035d64:	0705                	addi	a4,a4,1 # 2001 <RvExcFrameSize+0x1f71>
40035d66:	18e79923          	sh	a4,402(a5)
40035d6a:	4685                	li	a3,1
40035d6c:	b5e1                	j	40035c34 <tdefl_compress+0x4b0>
40035d6e:	4721                	li	a4,8
40035d70:	dc18                	sw	a4,56(s0)
40035d72:	5418                	lw	a4,40(s0)
40035d74:	00170693          	addi	a3,a4,1
40035d78:	d414                	sw	a3,40(s0)
40035d7a:	d458                	sw	a4,44(s0)
40035d7c:	bff1                	j	40035d58 <tdefl_compress+0x5d4>
40035d7e:	67c1                	lui	a5,0x10
40035d80:	00ffffb3          	and	t6,t6,a5
40035d84:	485c                	lw	a5,20(s0)
40035d86:	00ffefb3          	or	t6,t6,a5
40035d8a:	000f9663          	bnez	t6,40035d96 <tdefl_compress+0x612>
40035d8e:	07f00793          	li	a5,127
40035d92:	0ad7fa63          	bgeu	a5,a3,40035e46 <tdefl_compress+0x6c2>
40035d96:	5c5c                	lw	a5,60(s0)
40035d98:	ffd68713          	addi	a4,a3,-3
40035d9c:	167d                	addi	a2,a2,-1
40035d9e:	97b6                	add	a5,a5,a3
40035da0:	dc5c                	sw	a5,60(s0)
40035da2:	00e58023          	sb	a4,0(a1) # 2000 <RvExcFrameSize+0x1f70>
40035da6:	541c                	lw	a5,40(s0)
40035da8:	00865593          	srli	a1,a2,0x8
40035dac:	00c780a3          	sb	a2,1(a5) # 10001 <RvExcFrameSize+0xff71>
40035db0:	541c                	lw	a5,40(s0)
40035db2:	00b78123          	sb	a1,2(a5)
40035db6:	541c                	lw	a5,40(s0)
40035db8:	5448                	lw	a0,44(s0)
40035dba:	078d                	addi	a5,a5,3
40035dbc:	d41c                	sw	a5,40(s0)
40035dbe:	00054783          	lbu	a5,0(a0)
40035dc2:	8385                	srli	a5,a5,0x1
40035dc4:	f807e793          	ori	a5,a5,-128
40035dc8:	00f50023          	sb	a5,0(a0)
40035dcc:	5c1c                	lw	a5,56(s0)
40035dce:	17fd                	addi	a5,a5,-1
40035dd0:	c3bd                	beqz	a5,40035e36 <tdefl_compress+0x6b2>
40035dd2:	dc1c                	sw	a5,56(s0)
40035dd4:	07f5f513          	andi	a0,a1,127
40035dd8:	3ff1d5b7          	lui	a1,0x3ff1d
40035ddc:	1ff67793          	andi	a5,a2,511
40035de0:	3bc58593          	addi	a1,a1,956 # 3ff1d3bc <s_tdefl_large_dist_sym>
40035de4:	95aa                	add	a1,a1,a0
40035de6:	97da                	add	a5,a5,s6
40035de8:	1ff00513          	li	a0,511
40035dec:	0007c783          	lbu	a5,0(a5)
40035df0:	0005c583          	lbu	a1,0(a1)
40035df4:	00c57363          	bgeu	a0,a2,40035dfa <tdefl_compress+0x676>
40035df8:	87ae                	mv	a5,a1
40035dfa:	0786                	slli	a5,a5,0x1
40035dfc:	97a2                	add	a5,a5,s0
40035dfe:	6589                	lui	a1,0x2
40035e00:	97ae                	add	a5,a5,a1
40035e02:	3d27d603          	lhu	a2,978(a5)
40035e06:	0605                	addi	a2,a2,1
40035e08:	3cc79923          	sh	a2,978(a5)
40035e0c:	4789                	li	a5,2
40035e0e:	e2d7f3e3          	bgeu	a5,a3,40035c34 <tdefl_compress+0x4b0>
40035e12:	00171613          	slli	a2,a4,0x1
40035e16:	3ff1d737          	lui	a4,0x3ff1d
40035e1a:	53c70713          	addi	a4,a4,1340 # 3ff1d53c <s_tdefl_len_sym>
40035e1e:	9732                	add	a4,a4,a2
40035e20:	00075783          	lhu	a5,0(a4)
40035e24:	0786                	slli	a5,a5,0x1
40035e26:	97a2                	add	a5,a5,s0
40035e28:	97ae                	add	a5,a5,a1
40035e2a:	1927d703          	lhu	a4,402(a5)
40035e2e:	0705                	addi	a4,a4,1
40035e30:	18e79923          	sh	a4,402(a5)
40035e34:	b501                	j	40035c34 <tdefl_compress+0x4b0>
40035e36:	47a1                	li	a5,8
40035e38:	dc1c                	sw	a5,56(s0)
40035e3a:	541c                	lw	a5,40(s0)
40035e3c:	00178513          	addi	a0,a5,1
40035e40:	d408                	sw	a0,40(s0)
40035e42:	d45c                	sw	a5,44(s0)
40035e44:	bf41                	j	40035dd4 <tdefl_compress+0x650>
40035e46:	9522                	add	a0,a0,s0
40035e48:	09054783          	lbu	a5,144(a0)
40035e4c:	c470                	sw	a2,76(s0)
40035e4e:	c834                	sw	a3,80(s0)
40035e50:	c87c                	sw	a5,84(s0)
40035e52:	bf21                	j	40035d6a <tdefl_compress+0x5e6>
40035e54:	6795                	lui	a5,0x5
40035e56:	26a78793          	addi	a5,a5,618 # 526a <RvExcFrameSize+0x51da>
40035e5a:	97aa                	add	a5,a5,a0
40035e5c:	6b8d                	lui	s7,0x3
40035e5e:	c43e                	sw	a5,8(sp)
40035e60:	272b8793          	addi	a5,s7,626 # 3272 <RvExcFrameSize+0x31e2>
40035e64:	3ff1eb37          	lui	s6,0x3ff1e
40035e68:	97aa                	add	a5,a5,a0
40035e6a:	892e                	mv	s2,a1
40035e6c:	93cb0b13          	addi	s6,s6,-1732 # 3ff1d93c <s_tdefl_small_dist_sym>
40035e70:	c63e                	sw	a5,12(sp)
40035e72:	a00490e3          	bnez	s1,40035872 <tdefl_compress+0xee>
40035e76:	00098563          	beqz	s3,40035e80 <tdefl_compress+0x6fc>
40035e7a:	501c                	lw	a5,32(s0)
40035e7c:	9e079be3          	bnez	a5,40035872 <tdefl_compress+0xee>
40035e80:	09242223          	sw	s2,132(s0)
40035e84:	08942423          	sw	s1,136(s0)
40035e88:	b539                	j	40035c96 <tdefl_compress+0x512>
40035e8a:	07442023          	sw	s4,96(s0)
40035e8e:	478d                	li	a5,3
40035e90:	9cf99ce3          	bne	s3,a5,40035868 <tdefl_compress+0xe4>
40035e94:	6525                	lui	a0,0x9
40035e96:	27250513          	addi	a0,a0,626 # 9272 <RvExcFrameSize+0x91e2>
40035e9a:	6609                	lui	a2,0x2
40035e9c:	4581                	li	a1,0
40035e9e:	9522                	add	a0,a0,s0
40035ea0:	23f220ef          	jal	400588de <memset>
40035ea4:	6515                	lui	a0,0x5
40035ea6:	27250513          	addi	a0,a0,626 # 5272 <RvExcFrameSize+0x51e2>
40035eaa:	6611                	lui	a2,0x4
40035eac:	4581                	li	a1,0
40035eae:	9522                	add	a0,a0,s0
40035eb0:	22f220ef          	jal	400588de <memset>
40035eb4:	02042223          	sw	zero,36(s0)
40035eb8:	ba45                	j	40035868 <tdefl_compress+0xe4>
40035eba:	e60789e3          	beqz	a5,40035d2c <tdefl_compress+0x5a8>
40035ebe:	5c58                	lw	a4,60(s0)
40035ec0:	ffd78513          	addi	a0,a5,-3
40035ec4:	4474                	lw	a3,76(s0)
40035ec6:	973e                	add	a4,a4,a5
40035ec8:	dc58                	sw	a4,60(s0)
40035eca:	5418                	lw	a4,40(s0)
40035ecc:	16fd                	addi	a3,a3,-1
40035ece:	0086d613          	srli	a2,a3,0x8
40035ed2:	00a70023          	sb	a0,0(a4)
40035ed6:	5418                	lw	a4,40(s0)
40035ed8:	00d700a3          	sb	a3,1(a4)
40035edc:	5418                	lw	a4,40(s0)
40035ede:	00c70123          	sb	a2,2(a4)
40035ee2:	5418                	lw	a4,40(s0)
40035ee4:	070d                	addi	a4,a4,3
40035ee6:	d418                	sw	a4,40(s0)
40035ee8:	5458                	lw	a4,44(s0)
40035eea:	00074583          	lbu	a1,0(a4)
40035eee:	8185                	srli	a1,a1,0x1
40035ef0:	f805e593          	ori	a1,a1,-128
40035ef4:	00b70023          	sb	a1,0(a4)
40035ef8:	5c18                	lw	a4,56(s0)
40035efa:	177d                	addi	a4,a4,-1
40035efc:	e0070fe3          	beqz	a4,40035d1a <tdefl_compress+0x596>
40035f00:	dc18                	sw	a4,56(s0)
40035f02:	07f67593          	andi	a1,a2,127
40035f06:	3ff1d637          	lui	a2,0x3ff1d
40035f0a:	1ff6f713          	andi	a4,a3,511
40035f0e:	3bc60613          	addi	a2,a2,956 # 3ff1d3bc <s_tdefl_large_dist_sym>
40035f12:	962e                	add	a2,a2,a1
40035f14:	975a                	add	a4,a4,s6
40035f16:	1ff00593          	li	a1,511
40035f1a:	00074703          	lbu	a4,0(a4)
40035f1e:	00064603          	lbu	a2,0(a2)
40035f22:	00d5f363          	bgeu	a1,a3,40035f28 <tdefl_compress+0x7a4>
40035f26:	8732                	mv	a4,a2
40035f28:	0706                	slli	a4,a4,0x1
40035f2a:	9722                	add	a4,a4,s0
40035f2c:	6609                	lui	a2,0x2
40035f2e:	9732                	add	a4,a4,a2
40035f30:	3d275683          	lhu	a3,978(a4)
40035f34:	0685                	addi	a3,a3,1
40035f36:	3cd71923          	sh	a3,978(a4)
40035f3a:	4709                	li	a4,2
40035f3c:	02f77263          	bgeu	a4,a5,40035f60 <tdefl_compress+0x7dc>
40035f40:	3ff1d737          	lui	a4,0x3ff1d
40035f44:	0506                	slli	a0,a0,0x1
40035f46:	53c70713          	addi	a4,a4,1340 # 3ff1d53c <s_tdefl_len_sym>
40035f4a:	972a                	add	a4,a4,a0
40035f4c:	00075783          	lhu	a5,0(a4)
40035f50:	0786                	slli	a5,a5,0x1
40035f52:	97a2                	add	a5,a5,s0
40035f54:	97b2                	add	a5,a5,a2
40035f56:	1927d703          	lhu	a4,402(a5)
40035f5a:	0705                	addi	a4,a4,1
40035f5c:	18e79923          	sh	a4,402(a5)
40035f60:	4834                	lw	a3,80(s0)
40035f62:	16fd                	addi	a3,a3,-1
40035f64:	b1f1                	j	40035c30 <tdefl_compress+0x4ac>
40035f66:	4881                	li	a7,0
40035f68:	8646                	mv	a2,a7
40035f6a:	b6e1                	j	40035b32 <tdefl_compress+0x3ae>
40035f6c:	b1c6f3e3          	bgeu	a3,t3,40035a72 <tdefl_compress+0x2ee>
40035f70:	9f22                	add	t5,t5,s0
40035f72:	090f4283          	lbu	t0,144(t5) # 9090 <RvExcFrameSize+0x9000>
40035f76:	08ff4383          	lbu	t2,143(t5)
40035f7a:	8642                	mv	a2,a6
40035f7c:	86f2                	mv	a3,t3
40035f7e:	bcd5                	j	40035a72 <tdefl_compress+0x2ee>
40035f80:	8082                	ret
