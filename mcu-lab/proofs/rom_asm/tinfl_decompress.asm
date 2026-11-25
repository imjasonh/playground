
mcu-lab/.embuild/tools/esp-rom-elfs/20241011/esp32c3_rev3_rom.elf:     file format elf32-littleriscv


Disassembly of section .bt_text:

400345ee <tinfl_decompress>:
400345ee:	7111                	addi	sp,sp,-256
400345f0:	cc3e                	sw	a5,24(sp)
400345f2:	421c                	lw	a5,0(a2)
400345f4:	cde2                	sw	s8,216(sp)
400345f6:	c836                	sw	a3,16(sp)
400345f8:	00f58c33          	add	s8,a1,a5
400345fc:	47e2                	lw	a5,24(sp)
400345fe:	d9ca                	sw	s2,240(sp)
40034600:	d5d2                	sw	s4,232(sp)
40034602:	4394                	lw	a3,0(a5)
40034604:	cfde                	sw	s7,220(sp)
40034606:	cbe6                	sw	s9,212(sp)
40034608:	00d707b3          	add	a5,a4,a3
4003460c:	c63e                	sw	a5,12(sp)
4003460e:	00487793          	andi	a5,a6,4
40034612:	df86                	sw	ra,252(sp)
40034614:	dda2                	sw	s0,248(sp)
40034616:	dba6                	sw	s1,244(sp)
40034618:	d7ce                	sw	s3,236(sp)
4003461a:	d3d6                	sw	s5,228(sp)
4003461c:	d1da                	sw	s6,224(sp)
4003461e:	c9ea                	sw	s10,208(sp)
40034620:	c7ee                	sw	s11,204(sp)
40034622:	ca32                	sw	a2,20(sp)
40034624:	ce3e                	sw	a5,28(sp)
40034626:	892a                	mv	s2,a0
40034628:	8a2e                	mv	s4,a1
4003462a:	8cba                	mv	s9,a4
4003462c:	5bfd                	li	s7,-1
4003462e:	e791                	bnez	a5,4003463a <tinfl_decompress+0x4c>
40034630:	47c2                	lw	a5,16(sp)
40034632:	16fd                	addi	a3,a3,-1
40034634:	40f70bb3          	sub	s7,a4,a5
40034638:	9bb6                	add	s7,s7,a3
4003463a:	001b8513          	addi	a0,s7,1
4003463e:	017576b3          	and	a3,a0,s7
40034642:	e681                	bnez	a3,4003464a <tinfl_decompress+0x5c>
40034644:	47c2                	lw	a5,16(sp)
40034646:	02fcf863          	bgeu	s9,a5,40034676 <tinfl_decompress+0x88>
4003464a:	47e2                	lw	a5,24(sp)
4003464c:	5575                	li	a0,-3
4003464e:	0007a023          	sw	zero,0(a5)
40034652:	47d2                	lw	a5,20(sp)
40034654:	0007a023          	sw	zero,0(a5)
40034658:	50fe                	lw	ra,252(sp)
4003465a:	546e                	lw	s0,248(sp)
4003465c:	54de                	lw	s1,244(sp)
4003465e:	594e                	lw	s2,240(sp)
40034660:	59be                	lw	s3,236(sp)
40034662:	5a2e                	lw	s4,232(sp)
40034664:	5a9e                	lw	s5,228(sp)
40034666:	5b0e                	lw	s6,224(sp)
40034668:	4bfe                	lw	s7,220(sp)
4003466a:	4c6e                	lw	s8,216(sp)
4003466c:	4cde                	lw	s9,212(sp)
4003466e:	4d4e                	lw	s10,208(sp)
40034670:	4dbe                	lw	s11,204(sp)
40034672:	6111                	addi	sp,sp,256
40034674:	8082                	ret
40034676:	03c92783          	lw	a5,60(s2)
4003467a:	00092583          	lw	a1,0(s2)
4003467e:	03500613          	li	a2,53
40034682:	c43e                	sw	a5,8(sp)
40034684:	00492483          	lw	s1,4(s2)
40034688:	03892983          	lw	s3,56(s2)
4003468c:	02092d83          	lw	s11,32(s2)
40034690:	02492a83          	lw	s5,36(s2)
40034694:	02892d03          	lw	s10,40(s2)
40034698:	76b66de3          	bltu	a2,a1,40035612 <tinfl_decompress+0x1024>
4003469c:	3ff1d637          	lui	a2,0x3ff1d
400346a0:	fc860613          	addi	a2,a2,-56 # 3ff1cfc8 <crc8_le_table+0x100>
400346a4:	058a                	slli	a1,a1,0x2
400346a6:	95b2                	add	a1,a1,a2
400346a8:	4190                	lw	a2,0(a1)
400346aa:	8602                	jr	a2
400346ac:	4685                	li	a3,1
400346ae:	00d92e23          	sw	a3,28(s2)
400346b2:	00d92823          	sw	a3,16(s2)
400346b6:	00092623          	sw	zero,12(s2)
400346ba:	00092423          	sw	zero,8(s2)
400346be:	00187693          	andi	a3,a6,1
400346c2:	16068a63          	beqz	a3,40034836 <tinfl_decompress+0x248>
400346c6:	0d8a6b63          	bltu	s4,s8,4003479c <tinfl_decompress+0x1ae>
400346ca:	4981                	li	s3,0
400346cc:	4d01                	li	s10,0
400346ce:	4a81                	li	s5,0
400346d0:	4d81                	li	s11,0
400346d2:	4481                	li	s1,0
400346d4:	00287613          	andi	a2,a6,2
400346d8:	c65d                	beqz	a2,40034786 <tinfl_decompress+0x198>
400346da:	4785                	li	a5,1
400346dc:	00f92023          	sw	a5,0(s2)
400346e0:	8b66                	mv	s6,s9
400346e2:	8452                	mv	s0,s4
400346e4:	4505                	li	a0,1
400346e6:	47a2                	lw	a5,8(sp)
400346e8:	00992223          	sw	s1,4(s2)
400346ec:	03392c23          	sw	s3,56(s2)
400346f0:	02f92e23          	sw	a5,60(s2)
400346f4:	47d2                	lw	a5,20(sp)
400346f6:	03b92023          	sw	s11,32(s2)
400346fa:	03592223          	sw	s5,36(s2)
400346fe:	03a92423          	sw	s10,40(s2)
40034702:	41440433          	sub	s0,s0,s4
40034706:	c380                	sw	s0,0(a5)
40034708:	47e2                	lw	a5,24(sp)
4003470a:	419b0b33          	sub	s6,s6,s9
4003470e:	0167a023          	sw	s6,0(a5)
40034712:	00987793          	andi	a5,a6,9
40034716:	d3a9                	beqz	a5,40034658 <tinfl_decompress+0x6a>
40034718:	57fd                	li	a5,-1
4003471a:	f2f50fe3          	beq	a0,a5,40034658 <tinfl_decompress+0x6a>
4003471e:	6305                	lui	t1,0x1
40034720:	5b030313          	addi	t1,t1,1456 # 15b0 <RvExcFrameSize+0x1520>
40034724:	026b78b3          	remu	a7,s6,t1
40034728:	01c92683          	lw	a3,28(s2)
4003472c:	6e41                	lui	t3,0x10
4003472e:	4e9d                	li	t4,7
40034730:	01069f93          	slli	t6,a3,0x10
40034734:	010fdf93          	srli	t6,t6,0x10
40034738:	0106d613          	srli	a2,a3,0x10
4003473c:	1e45                	addi	t3,t3,-15 # fff1 <RvExcFrameSize+0xff61>
4003473e:	740b1ae3          	bnez	s6,40035692 <tinfl_decompress+0x10a4>
40034742:	01061693          	slli	a3,a2,0x10
40034746:	96fe                	add	a3,a3,t6
40034748:	00d92e23          	sw	a3,28(s2)
4003474c:	f511                	bnez	a0,40034658 <tinfl_decompress+0x6a>
4003474e:	00187813          	andi	a6,a6,1
40034752:	f00803e3          	beqz	a6,40034658 <tinfl_decompress+0x6a>
40034756:	01092783          	lw	a5,16(s2)
4003475a:	eef68fe3          	beq	a3,a5,40034658 <tinfl_decompress+0x6a>
4003475e:	5579                	li	a0,-2
40034760:	bde5                	j	40034658 <tinfl_decompress+0x6a>
40034762:	f78a79e3          	bgeu	s4,s8,400346d4 <tinfl_decompress+0xe6>
40034766:	000a4603          	lbu	a2,0(s4)
4003476a:	001a0413          	addi	s0,s4,1
4003476e:	00c92423          	sw	a2,8(s2)
40034772:	01846f63          	bltu	s0,s8,40034790 <tinfl_decompress+0x1a2>
40034776:	00287613          	andi	a2,a6,2
4003477a:	ca4d                	beqz	a2,4003482c <tinfl_decompress+0x23e>
4003477c:	4789                	li	a5,2
4003477e:	00f92023          	sw	a5,0(s2)
40034782:	8b66                	mv	s6,s9
40034784:	b785                	j	400346e4 <tinfl_decompress+0xf6>
40034786:	00092423          	sw	zero,8(s2)
4003478a:	8452                	mv	s0,s4
4003478c:	0b8a7063          	bgeu	s4,s8,4003482c <tinfl_decompress+0x23e>
40034790:	00044603          	lbu	a2,0(s0)
40034794:	0405                	addi	s0,s0,1
40034796:	00c92623          	sw	a2,12(s2)
4003479a:	a03d                	j	400347c8 <tinfl_decompress+0x1da>
4003479c:	000a4683          	lbu	a3,0(s4)
400347a0:	001a0413          	addi	s0,s4,1
400347a4:	4981                	li	s3,0
400347a6:	00d92423          	sw	a3,8(s2)
400347aa:	4d01                	li	s10,0
400347ac:	4a81                	li	s5,0
400347ae:	4d81                	li	s11,0
400347b0:	4481                	li	s1,0
400347b2:	b7c1                	j	40034772 <tinfl_decompress+0x184>
400347b4:	8452                	mv	s0,s4
400347b6:	b7c1                	j	40034776 <tinfl_decompress+0x188>
400347b8:	ff8a7ee3          	bgeu	s4,s8,400347b4 <tinfl_decompress+0x1c6>
400347bc:	000a4603          	lbu	a2,0(s4)
400347c0:	001a0413          	addi	s0,s4,1
400347c4:	00c92623          	sw	a2,12(s2)
400347c8:	00892603          	lw	a2,8(s2)
400347cc:	00c92303          	lw	t1,12(s2)
400347d0:	4e7d                	li	t3,31
400347d2:	00861593          	slli	a1,a2,0x8
400347d6:	959a                	add	a1,a1,t1
400347d8:	03c5f5b3          	remu	a1,a1,t3
400347dc:	02037313          	andi	t1,t1,32
400347e0:	0065e5b3          	or	a1,a1,t1
400347e4:	4305                	li	t1,1
400347e6:	e591                	bnez	a1,400347f2 <tinfl_decompress+0x204>
400347e8:	00f67593          	andi	a1,a2,15
400347ec:	15e1                	addi	a1,a1,-8
400347ee:	00b03333          	snez	t1,a1
400347f2:	00487793          	andi	a5,a6,4
400347f6:	8a9a                	mv	s5,t1
400347f8:	e385                	bnez	a5,40034818 <tinfl_decompress+0x22a>
400347fa:	8211                	srli	a2,a2,0x4
400347fc:	0621                	addi	a2,a2,8
400347fe:	4585                	li	a1,1
40034800:	00c595b3          	sll	a1,a1,a2
40034804:	6e21                	lui	t3,0x8
40034806:	4a85                	li	s5,1
40034808:	00be6663          	bltu	t3,a1,40034814 <tinfl_decompress+0x226>
4003480c:	00c55633          	srl	a2,a0,a2
40034810:	00163a93          	seqz	s5,a2
40034814:	01536ab3          	or	s5,t1,s5
40034818:	8b66                	mv	s6,s9
4003481a:	040a8263          	beqz	s5,4003485e <tinfl_decompress+0x270>
4003481e:	02400793          	li	a5,36
40034822:	00f92023          	sw	a5,0(s2)
40034826:	8b66                	mv	s6,s9
40034828:	557d                	li	a0,-1
4003482a:	bd75                	j	400346e6 <tinfl_decompress+0xf8>
4003482c:	00092623          	sw	zero,12(s2)
40034830:	bf61                	j	400347c8 <tinfl_decompress+0x1da>
40034832:	8452                	mv	s0,s4
40034834:	b7ed                	j	4003481e <tinfl_decompress+0x230>
40034836:	8b66                	mv	s6,s9
40034838:	8452                	mv	s0,s4
4003483a:	4981                	li	s3,0
4003483c:	4d01                	li	s10,0
4003483e:	4a81                	li	s5,0
40034840:	4d81                	li	s11,0
40034842:	4481                	li	s1,0
40034844:	07846963          	bltu	s0,s8,400348b6 <tinfl_decompress+0x2c8>
40034848:	00287593          	andi	a1,a6,2
4003484c:	4601                	li	a2,0
4003484e:	478d                	li	a5,3
40034850:	1e059b63          	bnez	a1,40034a46 <tinfl_decompress+0x458>
40034854:	00961633          	sll	a2,a2,s1
40034858:	00c9e9b3          	or	s3,s3,a2
4003485c:	04a1                	addi	s1,s1,8
4003485e:	4609                	li	a2,2
40034860:	fe9672e3          	bgeu	a2,s1,40034844 <tinfl_decompress+0x256>
40034864:	0079f613          	andi	a2,s3,7
40034868:	00c92a23          	sw	a2,20(s2)
4003486c:	8205                	srli	a2,a2,0x1
4003486e:	00c92c23          	sw	a2,24(s2)
40034872:	0039d993          	srli	s3,s3,0x3
40034876:	14f5                	addi	s1,s1,-3
40034878:	24061863          	bnez	a2,40034ac8 <tinfl_decompress+0x4da>
4003487c:	0074f613          	andi	a2,s1,7
40034880:	04c4fe63          	bgeu	s1,a2,400348dc <tinfl_decompress+0x2ee>
40034884:	05846863          	bltu	s0,s8,400348d4 <tinfl_decompress+0x2e6>
40034888:	00287593          	andi	a1,a6,2
4003488c:	4601                	li	a2,0
4003488e:	4795                	li	a5,5
40034890:	1a059b63          	bnez	a1,40034a46 <tinfl_decompress+0x458>
40034894:	00961633          	sll	a2,a2,s1
40034898:	00c9e9b3          	or	s3,s3,a2
4003489c:	04a1                	addi	s1,s1,8
4003489e:	bff9                	j	4003487c <tinfl_decompress+0x28e>
400348a0:	8b66                	mv	s6,s9
400348a2:	8452                	mv	s0,s4
400348a4:	b755                	j	40034848 <tinfl_decompress+0x25a>
400348a6:	ff8a7de3          	bgeu	s4,s8,400348a0 <tinfl_decompress+0x2b2>
400348aa:	001a0413          	addi	s0,s4,1
400348ae:	000a4603          	lbu	a2,0(s4)
400348b2:	8b66                	mv	s6,s9
400348b4:	b745                	j	40034854 <tinfl_decompress+0x266>
400348b6:	00044603          	lbu	a2,0(s0)
400348ba:	0405                	addi	s0,s0,1
400348bc:	bf61                	j	40034854 <tinfl_decompress+0x266>
400348be:	8b66                	mv	s6,s9
400348c0:	8452                	mv	s0,s4
400348c2:	b7d9                	j	40034888 <tinfl_decompress+0x29a>
400348c4:	ff8a7de3          	bgeu	s4,s8,400348be <tinfl_decompress+0x2d0>
400348c8:	001a0413          	addi	s0,s4,1
400348cc:	000a4603          	lbu	a2,0(s4)
400348d0:	8b66                	mv	s6,s9
400348d2:	b7c9                	j	40034894 <tinfl_decompress+0x2a6>
400348d4:	00044603          	lbu	a2,0(s0)
400348d8:	0405                	addi	s0,s0,1
400348da:	bf6d                	j	40034894 <tinfl_decompress+0x2a6>
400348dc:	0074f613          	andi	a2,s1,7
400348e0:	00c9d9b3          	srl	s3,s3,a2
400348e4:	98e1                	andi	s1,s1,-8
400348e6:	4a81                	li	s5,0
400348e8:	ccbd                	beqz	s1,40034966 <tinfl_decompress+0x378>
400348ea:	461d                	li	a2,7
400348ec:	02966f63          	bltu	a2,s1,4003492a <tinfl_decompress+0x33c>
400348f0:	03846963          	bltu	s0,s8,40034922 <tinfl_decompress+0x334>
400348f4:	00287593          	andi	a1,a6,2
400348f8:	4601                	li	a2,0
400348fa:	4799                	li	a5,6
400348fc:	14059563          	bnez	a1,40034a46 <tinfl_decompress+0x458>
40034900:	00961633          	sll	a2,a2,s1
40034904:	00c9e9b3          	or	s3,s3,a2
40034908:	04a1                	addi	s1,s1,8
4003490a:	b7c5                	j	400348ea <tinfl_decompress+0x2fc>
4003490c:	8b66                	mv	s6,s9
4003490e:	8452                	mv	s0,s4
40034910:	b7d5                	j	400348f4 <tinfl_decompress+0x306>
40034912:	ff8a7de3          	bgeu	s4,s8,4003490c <tinfl_decompress+0x31e>
40034916:	001a0413          	addi	s0,s4,1
4003491a:	000a4603          	lbu	a2,0(s4)
4003491e:	8b66                	mv	s6,s9
40034920:	b7c5                	j	40034900 <tinfl_decompress+0x312>
40034922:	00044603          	lbu	a2,0(s0)
40034926:	0405                	addi	s0,s0,1
40034928:	bfe1                	j	40034900 <tinfl_decompress+0x312>
4003492a:	015905b3          	add	a1,s2,s5
4003492e:	660d                	lui	a2,0x3
40034930:	962e                	add	a2,a2,a1
40034932:	93360023          	sb	s3,-1760(a2) # 2920 <RvExcFrameSize+0x2890>
40034936:	14e1                	addi	s1,s1,-8
40034938:	0089d993          	srli	s3,s3,0x8
4003493c:	0a85                	addi	s5,s5,1
4003493e:	460d                	li	a2,3
40034940:	fb5674e3          	bgeu	a2,s5,400348e8 <tinfl_decompress+0x2fa>
40034944:	660d                	lui	a2,0x3
40034946:	964a                	add	a2,a2,s2
40034948:	92065a83          	lhu	s5,-1760(a2) # 2920 <RvExcFrameSize+0x2890>
4003494c:	92265603          	lhu	a2,-1758(a2)
40034950:	fff64613          	not	a2,a2
40034954:	0642                	slli	a2,a2,0x10
40034956:	8241                	srli	a2,a2,0x10
40034958:	0aca8e63          	beq	s5,a2,40034a14 <tinfl_decompress+0x426>
4003495c:	02700793          	li	a5,39
40034960:	00f92023          	sw	a5,0(s2)
40034964:	b5d1                	j	40034828 <tinfl_decompress+0x23a>
40034966:	03846e63          	bltu	s0,s8,400349a2 <tinfl_decompress+0x3b4>
4003496a:	00287613          	andi	a2,a6,2
4003496e:	479d                	li	a5,7
40034970:	ea79                	bnez	a2,40034a46 <tinfl_decompress+0x458>
40034972:	015905b3          	add	a1,s2,s5
40034976:	660d                	lui	a2,0x3
40034978:	962e                	add	a2,a2,a1
4003497a:	92060023          	sb	zero,-1760(a2) # 2920 <RvExcFrameSize+0x2890>
4003497e:	bf7d                	j	4003493c <tinfl_decompress+0x34e>
40034980:	8b66                	mv	s6,s9
40034982:	8452                	mv	s0,s4
40034984:	b7dd                	j	4003496a <tinfl_decompress+0x37c>
40034986:	ff8a7de3          	bgeu	s4,s8,40034980 <tinfl_decompress+0x392>
4003498a:	000a4583          	lbu	a1,0(s4)
4003498e:	01590533          	add	a0,s2,s5
40034992:	660d                	lui	a2,0x3
40034994:	962a                	add	a2,a2,a0
40034996:	001a0413          	addi	s0,s4,1
4003499a:	92b60023          	sb	a1,-1760(a2) # 2920 <RvExcFrameSize+0x2890>
4003499e:	8b66                	mv	s6,s9
400349a0:	bf71                	j	4003493c <tinfl_decompress+0x34e>
400349a2:	00044583          	lbu	a1,0(s0)
400349a6:	01590533          	add	a0,s2,s5
400349aa:	660d                	lui	a2,0x3
400349ac:	962a                	add	a2,a2,a0
400349ae:	92b60023          	sb	a1,-1760(a2) # 2920 <RvExcFrameSize+0x2890>
400349b2:	0405                	addi	s0,s0,1
400349b4:	b761                	j	4003493c <tinfl_decompress+0x34e>
400349b6:	8b66                	mv	s6,s9
400349b8:	8452                	mv	s0,s4
400349ba:	b74d                	j	4003495c <tinfl_decompress+0x36e>
400349bc:	461d                	li	a2,7
400349be:	02966f63          	bltu	a2,s1,400349fc <tinfl_decompress+0x40e>
400349c2:	03846963          	bltu	s0,s8,400349f4 <tinfl_decompress+0x406>
400349c6:	00287593          	andi	a1,a6,2
400349ca:	4601                	li	a2,0
400349cc:	03300793          	li	a5,51
400349d0:	e9bd                	bnez	a1,40034a46 <tinfl_decompress+0x458>
400349d2:	00961633          	sll	a2,a2,s1
400349d6:	00c9e9b3          	or	s3,s3,a2
400349da:	04a1                	addi	s1,s1,8
400349dc:	b7c5                	j	400349bc <tinfl_decompress+0x3ce>
400349de:	8b66                	mv	s6,s9
400349e0:	8452                	mv	s0,s4
400349e2:	b7d5                	j	400349c6 <tinfl_decompress+0x3d8>
400349e4:	ff8a7de3          	bgeu	s4,s8,400349de <tinfl_decompress+0x3f0>
400349e8:	001a0413          	addi	s0,s4,1
400349ec:	000a4603          	lbu	a2,0(s4)
400349f0:	8b66                	mv	s6,s9
400349f2:	b7c5                	j	400349d2 <tinfl_decompress+0x3e4>
400349f4:	00044603          	lbu	a2,0(s0)
400349f8:	0405                	addi	s0,s0,1
400349fa:	bfe1                	j	400349d2 <tinfl_decompress+0x3e4>
400349fc:	0ff9fd93          	zext.b	s11,s3
40034a00:	14e1                	addi	s1,s1,-8
40034a02:	0089d993          	srli	s3,s3,0x8
40034a06:	47b2                	lw	a5,12(sp)
40034a08:	00fb7e63          	bgeu	s6,a5,40034a24 <tinfl_decompress+0x436>
40034a0c:	01bb0023          	sb	s11,0(s6)
40034a10:	1afd                	addi	s5,s5,-1
40034a12:	0b05                	addi	s6,s6,1
40034a14:	060a8f63          	beqz	s5,40034a92 <tinfl_decompress+0x4a4>
40034a18:	f0d5                	bnez	s1,400349bc <tinfl_decompress+0x3ce>
40034a1a:	47b2                	lw	a5,12(sp)
40034a1c:	02fb6f63          	bltu	s6,a5,40034a5a <tinfl_decompress+0x46c>
40034a20:	47a5                	li	a5,9
40034a22:	a019                	j	40034a28 <tinfl_decompress+0x43a>
40034a24:	03400793          	li	a5,52
40034a28:	00f92023          	sw	a5,0(s2)
40034a2c:	4509                	li	a0,2
40034a2e:	b965                	j	400346e6 <tinfl_decompress+0xf8>
40034a30:	8b66                	mv	s6,s9
40034a32:	8452                	mv	s0,s4
40034a34:	bfc9                	j	40034a06 <tinfl_decompress+0x418>
40034a36:	8b66                	mv	s6,s9
40034a38:	8452                	mv	s0,s4
40034a3a:	b7c5                	j	40034a1a <tinfl_decompress+0x42c>
40034a3c:	00287793          	andi	a5,a6,2
40034a40:	cb81                	beqz	a5,40034a50 <tinfl_decompress+0x462>
40034a42:	02600793          	li	a5,38
40034a46:	00f92023          	sw	a5,0(s2)
40034a4a:	b969                	j	400346e4 <tinfl_decompress+0xf6>
40034a4c:	8b66                	mv	s6,s9
40034a4e:	8452                	mv	s0,s4
40034a50:	02800793          	li	a5,40
40034a54:	b731                	j	40034960 <tinfl_decompress+0x372>
40034a56:	8b66                	mv	s6,s9
40034a58:	8452                	mv	s0,s4
40034a5a:	ff8471e3          	bgeu	s0,s8,40034a3c <tinfl_decompress+0x44e>
40034a5e:	47b2                	lw	a5,12(sp)
40034a60:	408c0333          	sub	t1,s8,s0
40034a64:	41678633          	sub	a2,a5,s6
40034a68:	00667363          	bgeu	a2,t1,40034a6e <tinfl_decompress+0x480>
40034a6c:	8332                	mv	t1,a2
40034a6e:	006af363          	bgeu	s5,t1,40034a74 <tinfl_decompress+0x486>
40034a72:	8356                	mv	t1,s5
40034a74:	861a                	mv	a2,t1
40034a76:	85a2                	mv	a1,s0
40034a78:	855a                	mv	a0,s6
40034a7a:	d242                	sw	a6,36(sp)
40034a7c:	d01a                	sw	t1,32(sp)
40034a7e:	53d230ef          	jal	400587ba <memcpy>
40034a82:	5302                	lw	t1,32(sp)
40034a84:	5812                	lw	a6,36(sp)
40034a86:	406a8ab3          	sub	s5,s5,t1
40034a8a:	941a                	add	s0,s0,t1
40034a8c:	9b1a                	add	s6,s6,t1
40034a8e:	f80a96e3          	bnez	s5,40034a1a <tinfl_decompress+0x42c>
40034a92:	01492603          	lw	a2,20(s2)
40034a96:	8a05                	andi	a2,a2,1
40034a98:	dc0603e3          	beqz	a2,4003485e <tinfl_decompress+0x270>
40034a9c:	00187613          	andi	a2,a6,1
40034aa0:	320606e3          	beqz	a2,400355cc <tinfl_decompress+0xfde>
40034aa4:	0074f613          	andi	a2,s1,7
40034aa8:	2ac4fbe3          	bgeu	s1,a2,4003555e <tinfl_decompress+0xf70>
40034aac:	2b8464e3          	bltu	s0,s8,40035554 <tinfl_decompress+0xf66>
40034ab0:	00287593          	andi	a1,a6,2
40034ab4:	4601                	li	a2,0
40034ab6:	02000793          	li	a5,32
40034aba:	f5d1                	bnez	a1,40034a46 <tinfl_decompress+0x458>
40034abc:	00961633          	sll	a2,a2,s1
40034ac0:	00c9e9b3          	or	s3,s3,a2
40034ac4:	04a1                	addi	s1,s1,8
40034ac6:	bff9                	j	40034aa4 <tinfl_decompress+0x4b6>
40034ac8:	458d                	li	a1,3
40034aca:	00b61763          	bne	a2,a1,40034ad8 <tinfl_decompress+0x4ea>
40034ace:	47a9                	li	a5,10
40034ad0:	bd41                	j	40034960 <tinfl_decompress+0x372>
40034ad2:	8b66                	mv	s6,s9
40034ad4:	8452                	mv	s0,s4
40034ad6:	bfe5                	j	40034ace <tinfl_decompress+0x4e0>
40034ad8:	4585                	li	a1,1
40034ada:	0ab61a63          	bne	a2,a1,40034b8e <tinfl_decompress+0x5a0>
40034ade:	12000613          	li	a2,288
40034ae2:	6505                	lui	a0,0x1
40034ae4:	02c92623          	sw	a2,44(s2)
40034ae8:	de050513          	addi	a0,a0,-544 # de0 <RvExcFrameSize+0xd50>
40034aec:	02000613          	li	a2,32
40034af0:	04090313          	addi	t1,s2,64
40034af4:	02c92823          	sw	a2,48(s2)
40034af8:	4595                	li	a1,5
40034afa:	954a                	add	a0,a0,s2
40034afc:	d242                	sw	a6,36(sp)
40034afe:	d01a                	sw	t1,32(sp)
40034b00:	5df230ef          	jal	400588de <memset>
40034b04:	5812                	lw	a6,36(sp)
40034b06:	5302                	lw	t1,32(sp)
40034b08:	0d090613          	addi	a2,s2,208
40034b0c:	45a1                	li	a1,8
40034b0e:	0305                	addi	t1,t1,1
40034b10:	feb30fa3          	sb	a1,-1(t1)
40034b14:	fec31de3          	bne	t1,a2,40034b0e <tinfl_decompress+0x520>
40034b18:	14090613          	addi	a2,s2,320
40034b1c:	45a5                	li	a1,9
40034b1e:	0305                	addi	t1,t1,1
40034b20:	feb30fa3          	sb	a1,-1(t1)
40034b24:	fec31de3          	bne	t1,a2,40034b1e <tinfl_decompress+0x530>
40034b28:	15890613          	addi	a2,s2,344
40034b2c:	459d                	li	a1,7
40034b2e:	0305                	addi	t1,t1,1
40034b30:	feb30fa3          	sb	a1,-1(t1)
40034b34:	fec31de3          	bne	t1,a2,40034b2e <tinfl_decompress+0x540>
40034b38:	16090613          	addi	a2,s2,352
40034b3c:	45a1                	li	a1,8
40034b3e:	0305                	addi	t1,t1,1
40034b40:	feb30fa3          	sb	a1,-1(t1)
40034b44:	fec31de3          	bne	t1,a2,40034b3e <tinfl_decompress+0x550>
40034b48:	01892303          	lw	t1,24(s2)
40034b4c:	16035063          	bgez	t1,40034cac <tinfl_decompress+0x6be>
40034b50:	4e0d                	li	t3,3
40034b52:	4e85                	li	t4,1
40034b54:	4339                	li	t1,14
40034b56:	408c0633          	sub	a2,s8,s0
40034b5a:	52ce5963          	bge	t3,a2,4003508c <tinfl_decompress+0xa9e>
40034b5e:	47b2                	lw	a5,12(sp)
40034b60:	41678633          	sub	a2,a5,s6
40034b64:	62cec463          	blt	t4,a2,4003518c <tinfl_decompress+0xb9e>
40034b68:	4639                	li	a2,14
40034b6a:	56966663          	bltu	a2,s1,400350d6 <tinfl_decompress+0xae8>
40034b6e:	00144603          	lbu	a2,1(s0)
40034b72:	00848593          	addi	a1,s1,8
40034b76:	0409                	addi	s0,s0,2
40034b78:	00b61633          	sll	a2,a2,a1
40034b7c:	ffe44583          	lbu	a1,-2(s0)
40034b80:	009595b3          	sll	a1,a1,s1
40034b84:	8e4d                	or	a2,a2,a1
40034b86:	00c9e9b3          	or	s3,s3,a2
40034b8a:	04c1                	addi	s1,s1,16
40034b8c:	a3a9                	j	400350d6 <tinfl_decompress+0xae8>
40034b8e:	4a81                	li	s5,0
40034b90:	3ff1e637          	lui	a2,0x3ff1e
40034b94:	b4060613          	addi	a2,a2,-1216 # 3ff1db40 <s_tdefl_small_dist_sym+0x204>
40034b98:	9656                	add	a2,a2,s5
40034b9a:	00064603          	lbu	a2,0(a2)
40034b9e:	02c4ff63          	bgeu	s1,a2,40034bdc <tinfl_decompress+0x5ee>
40034ba2:	03846963          	bltu	s0,s8,40034bd4 <tinfl_decompress+0x5e6>
40034ba6:	00287593          	andi	a1,a6,2
40034baa:	4601                	li	a2,0
40034bac:	47ad                	li	a5,11
40034bae:	e8059ce3          	bnez	a1,40034a46 <tinfl_decompress+0x458>
40034bb2:	00961633          	sll	a2,a2,s1
40034bb6:	00c9e9b3          	or	s3,s3,a2
40034bba:	04a1                	addi	s1,s1,8
40034bbc:	bfd1                	j	40034b90 <tinfl_decompress+0x5a2>
40034bbe:	8b66                	mv	s6,s9
40034bc0:	8452                	mv	s0,s4
40034bc2:	b7d5                	j	40034ba6 <tinfl_decompress+0x5b8>
40034bc4:	ff8a7de3          	bgeu	s4,s8,40034bbe <tinfl_decompress+0x5d0>
40034bc8:	001a0413          	addi	s0,s4,1
40034bcc:	000a4603          	lbu	a2,0(s4)
40034bd0:	8b66                	mv	s6,s9
40034bd2:	b7c5                	j	40034bb2 <tinfl_decompress+0x5c4>
40034bd4:	00044603          	lbu	a2,0(s0)
40034bd8:	0405                	addi	s0,s0,1
40034bda:	bfe1                	j	40034bb2 <tinfl_decompress+0x5c4>
40034bdc:	3ff1e637          	lui	a2,0x3ff1e
40034be0:	b4060613          	addi	a2,a2,-1216 # 3ff1db40 <s_tdefl_small_dist_sym+0x204>
40034be4:	9656                	add	a2,a2,s5
40034be6:	00064583          	lbu	a1,0(a2)
40034bea:	4605                	li	a2,1
40034bec:	002a9313          	slli	t1,s5,0x2
40034bf0:	00b61633          	sll	a2,a2,a1
40034bf4:	167d                	addi	a2,a2,-1
40034bf6:	01367533          	and	a0,a2,s3
40034bfa:	8c8d                	sub	s1,s1,a1
40034bfc:	00b9d9b3          	srl	s3,s3,a1
40034c00:	3ff1d5b7          	lui	a1,0x3ff1d
40034c04:	33058593          	addi	a1,a1,816 # 3ff1d330 <s_min_table_sizes.2684>
40034c08:	959a                	add	a1,a1,t1
40034c0a:	418c                	lw	a1,0(a1)
40034c0c:	008a8613          	addi	a2,s5,8
40034c10:	060a                	slli	a2,a2,0x2
40034c12:	964a                	add	a2,a2,s2
40034c14:	952e                	add	a0,a0,a1
40034c16:	c648                	sw	a0,12(a2)
40034c18:	0a85                	addi	s5,s5,1
40034c1a:	4609                	li	a2,2
40034c1c:	f7567ae3          	bgeu	a2,s5,40034b90 <tinfl_decompress+0x5a2>
40034c20:	6509                	lui	a0,0x2
40034c22:	b8050513          	addi	a0,a0,-1152 # 1b80 <RvExcFrameSize+0x1af0>
40034c26:	12000613          	li	a2,288
40034c2a:	4581                	li	a1,0
40034c2c:	954a                	add	a0,a0,s2
40034c2e:	d042                	sw	a6,32(sp)
40034c30:	4af230ef          	jal	400588de <memset>
40034c34:	5802                	lw	a6,32(sp)
40034c36:	4a81                	li	s5,0
40034c38:	03492603          	lw	a2,52(s2)
40034c3c:	02cae563          	bltu	s5,a2,40034c66 <tinfl_decompress+0x678>
40034c40:	464d                	li	a2,19
40034c42:	02c92a23          	sw	a2,52(s2)
40034c46:	b709                	j	40034b48 <tinfl_decompress+0x55a>
40034c48:	8b66                	mv	s6,s9
40034c4a:	8452                	mv	s0,s4
40034c4c:	a015                	j	40034c70 <tinfl_decompress+0x682>
40034c4e:	ff8a7de3          	bgeu	s4,s8,40034c48 <tinfl_decompress+0x65a>
40034c52:	000a4603          	lbu	a2,0(s4)
40034c56:	001a0413          	addi	s0,s4,1
40034c5a:	8b66                	mv	s6,s9
40034c5c:	00961633          	sll	a2,a2,s1
40034c60:	00c9e9b3          	or	s3,s3,a2
40034c64:	04a1                	addi	s1,s1,8
40034c66:	4609                	li	a2,2
40034c68:	00966e63          	bltu	a2,s1,40034c84 <tinfl_decompress+0x696>
40034c6c:	01846863          	bltu	s0,s8,40034c7c <tinfl_decompress+0x68e>
40034c70:	00287593          	andi	a1,a6,2
40034c74:	4601                	li	a2,0
40034c76:	d1fd                	beqz	a1,40034c5c <tinfl_decompress+0x66e>
40034c78:	47b9                	li	a5,14
40034c7a:	b3f1                	j	40034a46 <tinfl_decompress+0x458>
40034c7c:	00044603          	lbu	a2,0(s0)
40034c80:	0405                	addi	s0,s0,1
40034c82:	bfe9                	j	40034c5c <tinfl_decompress+0x66e>
40034c84:	3ff1d637          	lui	a2,0x3ff1d
40034c88:	2a060613          	addi	a2,a2,672 # 3ff1d2a0 <s_length_dezigzag.2683>
40034c8c:	9656                	add	a2,a2,s5
40034c8e:	00064603          	lbu	a2,0(a2)
40034c92:	0079f593          	andi	a1,s3,7
40034c96:	14f5                	addi	s1,s1,-3
40034c98:	00c90533          	add	a0,s2,a2
40034c9c:	6609                	lui	a2,0x2
40034c9e:	962a                	add	a2,a2,a0
40034ca0:	b8b60023          	sb	a1,-1152(a2) # 1b80 <RvExcFrameSize+0x1af0>
40034ca4:	0039d993          	srli	s3,s3,0x3
40034ca8:	0a85                	addi	s5,s5,1
40034caa:	b779                	j	40034c38 <tinfl_decompress+0x64a>
40034cac:	04000613          	li	a2,64
40034cb0:	4581                	li	a1,0
40034cb2:	1868                	addi	a0,sp,60
40034cb4:	d442                	sw	a6,40(sp)
40034cb6:	d01a                	sw	t1,32(sp)
40034cb8:	427230ef          	jal	400588de <memset>
40034cbc:	5302                	lw	t1,32(sp)
40034cbe:	6e05                	lui	t3,0x1
40034cc0:	da0e0e93          	addi	t4,t3,-608 # da0 <RvExcFrameSize+0xd10>
40034cc4:	03d30eb3          	mul	t4,t1,t4
40034cc8:	800e0613          	addi	a2,t3,-2048
40034ccc:	4581                	li	a1,0
40034cce:	d21a                	sw	t1,36(sp)
40034cd0:	160e8513          	addi	a0,t4,352
40034cd4:	954a                	add	a0,a0,s2
40034cd6:	d076                	sw	t4,32(sp)
40034cd8:	407230ef          	jal	400588de <memset>
40034cdc:	5e82                	lw	t4,32(sp)
40034cde:	6e05                	lui	t3,0x1
40034ce0:	960e0513          	addi	a0,t3,-1696 # 960 <RvExcFrameSize+0x8d0>
40034ce4:	9576                	add	a0,a0,t4
40034ce6:	48000613          	li	a2,1152
40034cea:	4581                	li	a1,0
40034cec:	954a                	add	a0,a0,s2
40034cee:	3f1230ef          	jal	400588de <memset>
40034cf2:	01892783          	lw	a5,24(s2)
40034cf6:	5e82                	lw	t4,32(sp)
40034cf8:	5312                	lw	t1,36(sp)
40034cfa:	00878613          	addi	a2,a5,8
40034cfe:	060a                	slli	a2,a2,0x2
40034d00:	964a                	add	a2,a2,s2
40034d02:	00c62e03          	lw	t3,12(a2)
40034d06:	5822                	lw	a6,40(sp)
40034d08:	01d90733          	add	a4,s2,t4
40034d0c:	86ba                	mv	a3,a4
40034d0e:	85ba                	mv	a1,a4
40034d10:	4e81                	li	t4,0
40034d12:	0585                	addi	a1,a1,1
40034d14:	03de1e63          	bne	t3,t4,40034d50 <tinfl_decompress+0x762>
40034d18:	c102                	sw	zero,128(sp)
40034d1a:	de82                	sw	zero,124(sp)
40034d1c:	186c                	addi	a1,sp,60
40034d1e:	07c10f13          	addi	t5,sp,124
40034d22:	07810f93          	addi	t6,sp,120
40034d26:	4601                	li	a2,0
40034d28:	4e01                	li	t3,0
40034d2a:	41c8                	lw	a0,4(a1)
40034d2c:	0591                	addi	a1,a1,4
40034d2e:	0f11                	addi	t5,t5,4
40034d30:	962a                	add	a2,a2,a0
40034d32:	0606                	slli	a2,a2,0x1
40034d34:	00cf2223          	sw	a2,4(t5)
40034d38:	9e2a                	add	t3,t3,a0
40034d3a:	febf98e3          	bne	t6,a1,40034d2a <tinfl_decompress+0x73c>
40034d3e:	65c1                	lui	a1,0x10
40034d40:	10b60063          	beq	a2,a1,40034e40 <tinfl_decompress+0x852>
40034d44:	4605                	li	a2,1
40034d46:	0fc67d63          	bgeu	a2,t3,40034e40 <tinfl_decompress+0x852>
40034d4a:	02300793          	li	a5,35
40034d4e:	b909                	j	40034960 <tinfl_decompress+0x372>
40034d50:	03f5c603          	lbu	a2,63(a1) # 1003f <RvExcFrameSize+0xffaf>
40034d54:	0188                	addi	a0,sp,192
40034d56:	0e85                	addi	t4,t4,1
40034d58:	060a                	slli	a2,a2,0x2
40034d5a:	962a                	add	a2,a2,a0
40034d5c:	f7c62503          	lw	a0,-132(a2)
40034d60:	0505                	addi	a0,a0,1
40034d62:	f6a62e23          	sw	a0,-132(a2)
40034d66:	b775                	j	40034d12 <tinfl_decompress+0x724>
40034d68:	8b66                	mv	s6,s9
40034d6a:	8452                	mv	s0,s4
40034d6c:	bff9                	j	40034d4a <tinfl_decompress+0x75c>
40034d6e:	0406c503          	lbu	a0,64(a3)
40034d72:	8faa                	mv	t6,a0
40034d74:	c921                	beqz	a0,40034dc4 <tinfl_decompress+0x7d6>
40034d76:	0c010f13          	addi	t5,sp,192
40034d7a:	00251613          	slli	a2,a0,0x2
40034d7e:	967a                	add	a2,a2,t5
40034d80:	fbc62f03          	lw	t5,-68(a2)
40034d84:	001f0293          	addi	t0,t5,1
40034d88:	fa562e23          	sw	t0,-68(a2)
40034d8c:	82aa                	mv	t0,a0
40034d8e:	4601                	li	a2,0
40034d90:	001f7393          	andi	t2,t5,1
40034d94:	0606                	slli	a2,a2,0x1
40034d96:	12fd                	addi	t0,t0,-1
40034d98:	00c3e633          	or	a2,t2,a2
40034d9c:	001f5f13          	srli	t5,t5,0x1
40034da0:	fe0298e3          	bnez	t0,40034d90 <tinfl_decompress+0x7a2>
40034da4:	04a8e063          	bltu	a7,a0,40034de4 <tinfl_decompress+0x7f6>
40034da8:	00951f13          	slli	t5,a0,0x9
40034dac:	01cf6f33          	or	t5,t5,t3
40034db0:	0f42                	slli	t5,t5,0x10
40034db2:	4f85                	li	t6,1
40034db4:	410f5f13          	srai	t5,t5,0x10
40034db8:	00af9533          	sll	a0,t6,a0
40034dbc:	3ff00f93          	li	t6,1023
40034dc0:	00cffb63          	bgeu	t6,a2,40034dd6 <tinfl_decompress+0x7e8>
40034dc4:	0e05                	addi	t3,t3,1
40034dc6:	0685                	addi	a3,a3,1
40034dc8:	fbce93e3          	bne	t4,t3,40034d6e <tinfl_decompress+0x780>
40034dcc:	4609                	li	a2,2
40034dce:	14c79e63          	bne	a5,a2,40034f2a <tinfl_decompress+0x93c>
40034dd2:	4a81                	li	s5,0
40034dd4:	a231                	j	40034ee0 <tinfl_decompress+0x8f2>
40034dd6:	00161f93          	slli	t6,a2,0x1
40034dda:	9fba                	add	t6,t6,a4
40034ddc:	17ef9023          	sh	t5,352(t6)
40034de0:	962a                	add	a2,a2,a0
40034de2:	bfe9                	j	40034dbc <tinfl_decompress+0x7ce>
40034de4:	3ff67f13          	andi	t5,a2,1023
40034de8:	9f1a                	add	t5,t5,t1
40034dea:	0f06                	slli	t5,t5,0x1
40034dec:	9f4a                	add	t5,t5,s2
40034dee:	160f1503          	lh	a0,352(t5)
40034df2:	e509                	bnez	a0,40034dfc <tinfl_decompress+0x80e>
40034df4:	16bf1023          	sh	a1,352(t5)
40034df8:	852e                	mv	a0,a1
40034dfa:	15f9                	addi	a1,a1,-2
40034dfc:	8225                	srli	a2,a2,0x9
40034dfe:	8205                	srli	a2,a2,0x1
40034e00:	00167f13          	andi	t5,a2,1
40034e04:	41e50533          	sub	a0,a0,t5
40034e08:	4f2d                	li	t5,11
40034e0a:	fff54513          	not	a0,a0
40034e0e:	01ef9a63          	bne	t6,t5,40034e22 <tinfl_decompress+0x834>
40034e12:	951a                	add	a0,a0,t1
40034e14:	4b050513          	addi	a0,a0,1200
40034e18:	0506                	slli	a0,a0,0x1
40034e1a:	954a                	add	a0,a0,s2
40034e1c:	01c51023          	sh	t3,0(a0)
40034e20:	b755                	j	40034dc4 <tinfl_decompress+0x7d6>
40034e22:	00650f33          	add	t5,a0,t1
40034e26:	0f06                	slli	t5,t5,0x1
40034e28:	6505                	lui	a0,0x1
40034e2a:	9f4a                	add	t5,t5,s2
40034e2c:	9f2a                	add	t5,t5,a0
40034e2e:	960f1503          	lh	a0,-1696(t5)
40034e32:	e509                	bnez	a0,40034e3c <tinfl_decompress+0x84e>
40034e34:	96bf1023          	sh	a1,-1696(t5)
40034e38:	852e                	mv	a0,a1
40034e3a:	15f9                	addi	a1,a1,-2
40034e3c:	1ffd                	addi	t6,t6,-1
40034e3e:	b7c1                	j	40034dfe <tinfl_decompress+0x810>
40034e40:	6d000613          	li	a2,1744
40034e44:	4e01                	li	t3,0
40034e46:	55fd                	li	a1,-1
40034e48:	48a9                	li	a7,10
40034e4a:	02c30333          	mul	t1,t1,a2
40034e4e:	bfad                	j	40034dc8 <tinfl_decompress+0x7da>
40034e50:	4639                	li	a2,14
40034e52:	04966963          	bltu	a2,s1,40034ea4 <tinfl_decompress+0x8b6>
40034e56:	408c0633          	sub	a2,s8,s0
40034e5a:	4585                	li	a1,1
40034e5c:	12c5c763          	blt	a1,a2,40034f8a <tinfl_decompress+0x99c>
40034e60:	6505                	lui	a0,0x1
40034e62:	3ff9f613          	andi	a2,s3,1023
40034e66:	e5050593          	addi	a1,a0,-432 # e50 <RvExcFrameSize+0xdc0>
40034e6a:	962e                	add	a2,a2,a1
40034e6c:	0606                	slli	a2,a2,0x1
40034e6e:	964a                	add	a2,a2,s2
40034e70:	00061e03          	lh	t3,0(a2)
40034e74:	0c0e4163          	bltz	t3,40034f36 <tinfl_decompress+0x948>
40034e78:	409e5e13          	srai	t3,t3,0x9
40034e7c:	000e0463          	beqz	t3,40034e84 <tinfl_decompress+0x896>
40034e80:	03c4f263          	bgeu	s1,t3,40034ea4 <tinfl_decompress+0x8b6>
40034e84:	0f846f63          	bltu	s0,s8,40034f82 <tinfl_decompress+0x994>
40034e88:	00287593          	andi	a1,a6,2
40034e8c:	4601                	li	a2,0
40034e8e:	47c1                	li	a5,16
40034e90:	ba059be3          	bnez	a1,40034a46 <tinfl_decompress+0x458>
40034e94:	00961633          	sll	a2,a2,s1
40034e98:	00c9e9b3          	or	s3,s3,a2
40034e9c:	04a1                	addi	s1,s1,8
40034e9e:	4639                	li	a2,14
40034ea0:	fc9670e3          	bgeu	a2,s1,40034e60 <tinfl_decompress+0x872>
40034ea4:	6505                	lui	a0,0x1
40034ea6:	3ff9f613          	andi	a2,s3,1023
40034eaa:	e5050593          	addi	a1,a0,-432 # e50 <RvExcFrameSize+0xdc0>
40034eae:	962e                	add	a2,a2,a1
40034eb0:	0606                	slli	a2,a2,0x1
40034eb2:	964a                	add	a2,a2,s2
40034eb4:	00061303          	lh	t1,0(a2)
40034eb8:	0e034963          	bltz	t1,40034faa <tinfl_decompress+0x9bc>
40034ebc:	40935593          	srai	a1,t1,0x9
40034ec0:	1ff37313          	andi	t1,t1,511
40034ec4:	463d                	li	a2,15
40034ec6:	8d9a                	mv	s11,t1
40034ec8:	00b9d9b3          	srl	s3,s3,a1
40034ecc:	8c8d                	sub	s1,s1,a1
40034ece:	10664263          	blt	a2,t1,40034fd2 <tinfl_decompress+0x9e4>
40034ed2:	015905b3          	add	a1,s2,s5
40034ed6:	660d                	lui	a2,0x3
40034ed8:	962e                	add	a2,a2,a1
40034eda:	92660223          	sb	t1,-1756(a2) # 2924 <RvExcFrameSize+0x2894>
40034ede:	0a85                	addi	s5,s5,1
40034ee0:	02c92e03          	lw	t3,44(s2)
40034ee4:	03092e83          	lw	t4,48(s2)
40034ee8:	01de0633          	add	a2,t3,t4
40034eec:	f6cae2e3          	bltu	s5,a2,40034e50 <tinfl_decompress+0x862>
40034ef0:	19561c63          	bne	a2,s5,40035088 <tinfl_decompress+0xa9a>
40034ef4:	630d                	lui	t1,0x3
40034ef6:	92430313          	addi	t1,t1,-1756 # 2924 <RvExcFrameSize+0x2894>
40034efa:	934a                	add	t1,t1,s2
40034efc:	8672                	mv	a2,t3
40034efe:	859a                	mv	a1,t1
40034f00:	04090513          	addi	a0,s2,64
40034f04:	d642                	sw	a6,44(sp)
40034f06:	d476                	sw	t4,40(sp)
40034f08:	d272                	sw	t3,36(sp)
40034f0a:	d01a                	sw	t1,32(sp)
40034f0c:	0af230ef          	jal	400587ba <memcpy>
40034f10:	5ea2                	lw	t4,40(sp)
40034f12:	5302                	lw	t1,32(sp)
40034f14:	5e12                	lw	t3,36(sp)
40034f16:	6505                	lui	a0,0x1
40034f18:	de050513          	addi	a0,a0,-544 # de0 <RvExcFrameSize+0xd50>
40034f1c:	8676                	mv	a2,t4
40034f1e:	01c305b3          	add	a1,t1,t3
40034f22:	954a                	add	a0,a0,s2
40034f24:	097230ef          	jal	400587ba <memcpy>
40034f28:	5832                	lw	a6,44(sp)
40034f2a:	01892603          	lw	a2,24(s2)
40034f2e:	167d                	addi	a2,a2,-1
40034f30:	00c92c23          	sw	a2,24(s2)
40034f34:	b911                	j	40034b48 <tinfl_decompress+0x55a>
40034f36:	4629                	li	a2,10
40034f38:	f49676e3          	bgeu	a2,s1,40034e84 <tinfl_decompress+0x896>
40034f3c:	45a9                	li	a1,10
40034f3e:	25050513          	addi	a0,a0,592
40034f42:	00b9d633          	srl	a2,s3,a1
40034f46:	fffe4e13          	not	t3,t3
40034f4a:	8a05                	andi	a2,a2,1
40034f4c:	9672                	add	a2,a2,t3
40034f4e:	962a                	add	a2,a2,a0
40034f50:	0606                	slli	a2,a2,0x1
40034f52:	964a                	add	a2,a2,s2
40034f54:	00061e03          	lh	t3,0(a2)
40034f58:	00158313          	addi	t1,a1,1
40034f5c:	f40e54e3          	bgez	t3,40034ea4 <tinfl_decompress+0x8b6>
40034f60:	00258613          	addi	a2,a1,2
40034f64:	859a                	mv	a1,t1
40034f66:	fcc4fee3          	bgeu	s1,a2,40034f42 <tinfl_decompress+0x954>
40034f6a:	bf29                	j	40034e84 <tinfl_decompress+0x896>
40034f6c:	8b66                	mv	s6,s9
40034f6e:	8452                	mv	s0,s4
40034f70:	bf21                	j	40034e88 <tinfl_decompress+0x89a>
40034f72:	ff8a7de3          	bgeu	s4,s8,40034f6c <tinfl_decompress+0x97e>
40034f76:	001a0413          	addi	s0,s4,1
40034f7a:	000a4603          	lbu	a2,0(s4)
40034f7e:	8b66                	mv	s6,s9
40034f80:	bf11                	j	40034e94 <tinfl_decompress+0x8a6>
40034f82:	00044603          	lbu	a2,0(s0)
40034f86:	0405                	addi	s0,s0,1
40034f88:	b731                	j	40034e94 <tinfl_decompress+0x8a6>
40034f8a:	00144603          	lbu	a2,1(s0)
40034f8e:	00848593          	addi	a1,s1,8
40034f92:	0409                	addi	s0,s0,2
40034f94:	00b61633          	sll	a2,a2,a1
40034f98:	ffe44583          	lbu	a1,-2(s0)
40034f9c:	009595b3          	sll	a1,a1,s1
40034fa0:	8e4d                	or	a2,a2,a1
40034fa2:	00c9e9b3          	or	s3,s3,a2
40034fa6:	04c1                	addi	s1,s1,16
40034fa8:	bdf5                	j	40034ea4 <tinfl_decompress+0x8b6>
40034faa:	4629                	li	a2,10
40034fac:	25050513          	addi	a0,a0,592
40034fb0:	00160593          	addi	a1,a2,1
40034fb4:	00c9d633          	srl	a2,s3,a2
40034fb8:	fff34313          	not	t1,t1
40034fbc:	8a05                	andi	a2,a2,1
40034fbe:	961a                	add	a2,a2,t1
40034fc0:	962a                	add	a2,a2,a0
40034fc2:	0606                	slli	a2,a2,0x1
40034fc4:	964a                	add	a2,a2,s2
40034fc6:	00061303          	lh	t1,0(a2)
40034fca:	862e                	mv	a2,a1
40034fcc:	fe0342e3          	bltz	t1,40034fb0 <tinfl_decompress+0x9c2>
40034fd0:	bdd5                	j	40034ec4 <tinfl_decompress+0x8d6>
40034fd2:	4641                	li	a2,16
40034fd4:	00c31963          	bne	t1,a2,40034fe6 <tinfl_decompress+0x9f8>
40034fd8:	000a9763          	bnez	s5,40034fe6 <tinfl_decompress+0x9f8>
40034fdc:	47c5                	li	a5,17
40034fde:	b249                	j	40034960 <tinfl_decompress+0x372>
40034fe0:	8b66                	mv	s6,s9
40034fe2:	8452                	mv	s0,s4
40034fe4:	bfe5                	j	40034fdc <tinfl_decompress+0x9ee>
40034fe6:	3ff1e637          	lui	a2,0x3ff1e
40034fea:	b3c60613          	addi	a2,a2,-1220 # 3ff1db3c <s_tdefl_small_dist_sym+0x200>
40034fee:	961a                	add	a2,a2,t1
40034ff0:	ff064d03          	lbu	s10,-16(a2)
40034ff4:	03a4ff63          	bgeu	s1,s10,40035032 <tinfl_decompress+0xa44>
40034ff8:	03846963          	bltu	s0,s8,4003502a <tinfl_decompress+0xa3c>
40034ffc:	00287593          	andi	a1,a6,2
40035000:	4601                	li	a2,0
40035002:	47c9                	li	a5,18
40035004:	a40591e3          	bnez	a1,40034a46 <tinfl_decompress+0x458>
40035008:	00961633          	sll	a2,a2,s1
4003500c:	00c9e9b3          	or	s3,s3,a2
40035010:	04a1                	addi	s1,s1,8
40035012:	b7cd                	j	40034ff4 <tinfl_decompress+0xa06>
40035014:	8b66                	mv	s6,s9
40035016:	8452                	mv	s0,s4
40035018:	b7d5                	j	40034ffc <tinfl_decompress+0xa0e>
4003501a:	ff8a7de3          	bgeu	s4,s8,40035014 <tinfl_decompress+0xa26>
4003501e:	001a0413          	addi	s0,s4,1
40035022:	000a4603          	lbu	a2,0(s4)
40035026:	8b66                	mv	s6,s9
40035028:	b7c5                	j	40035008 <tinfl_decompress+0xa1a>
4003502a:	00044603          	lbu	a2,0(s0)
4003502e:	0405                	addi	s0,s0,1
40035030:	bfe1                	j	40035008 <tinfl_decompress+0xa1a>
40035032:	3ff1e5b7          	lui	a1,0x3ff1e
40035036:	b4458593          	addi	a1,a1,-1212 # 3ff1db44 <s_tdefl_small_dist_sym+0x208>
4003503a:	95ee                	add	a1,a1,s11
4003503c:	4605                	li	a2,1
4003503e:	ff05c303          	lbu	t1,-16(a1)
40035042:	01a61633          	sll	a2,a2,s10
40035046:	167d                	addi	a2,a2,-1
40035048:	01367633          	and	a2,a2,s3
4003504c:	9332                	add	t1,t1,a2
4003504e:	660d                	lui	a2,0x3
40035050:	92460513          	addi	a0,a2,-1756 # 2924 <RvExcFrameSize+0x2894>
40035054:	954a                	add	a0,a0,s2
40035056:	4e41                	li	t3,16
40035058:	01a9d9b3          	srl	s3,s3,s10
4003505c:	41a484b3          	sub	s1,s1,s10
40035060:	9556                	add	a0,a0,s5
40035062:	4581                	li	a1,0
40035064:	01cd9763          	bne	s11,t3,40035072 <tinfl_decompress+0xa84>
40035068:	015905b3          	add	a1,s2,s5
4003506c:	962e                	add	a2,a2,a1
4003506e:	92364583          	lbu	a1,-1757(a2)
40035072:	861a                	mv	a2,t1
40035074:	d242                	sw	a6,36(sp)
40035076:	d01a                	sw	t1,32(sp)
40035078:	067230ef          	jal	400588de <memset>
4003507c:	5302                	lw	t1,32(sp)
4003507e:	5812                	lw	a6,36(sp)
40035080:	9a9a                	add	s5,s5,t1
40035082:	bdb9                	j	40034ee0 <tinfl_decompress+0x8f2>
40035084:	8b66                	mv	s6,s9
40035086:	8452                	mv	s0,s4
40035088:	47d5                	li	a5,21
4003508a:	b8d9                	j	40034960 <tinfl_decompress+0x372>
4003508c:	45b9                	li	a1,14
4003508e:	0495e463          	bltu	a1,s1,400350d6 <tinfl_decompress+0xae8>
40035092:	4585                	li	a1,1
40035094:	acc5cde3          	blt	a1,a2,40034b6e <tinfl_decompress+0x580>
40035098:	3ff9f613          	andi	a2,s3,1023
4003509c:	0b060613          	addi	a2,a2,176
400350a0:	0606                	slli	a2,a2,0x1
400350a2:	964a                	add	a2,a2,s2
400350a4:	00061303          	lh	t1,0(a2)
400350a8:	06034363          	bltz	t1,4003510e <tinfl_decompress+0xb20>
400350ac:	40935613          	srai	a2,t1,0x9
400350b0:	c219                	beqz	a2,400350b6 <tinfl_decompress+0xac8>
400350b2:	02c4f263          	bgeu	s1,a2,400350d6 <tinfl_decompress+0xae8>
400350b6:	0b846063          	bltu	s0,s8,40035156 <tinfl_decompress+0xb68>
400350ba:	00287593          	andi	a1,a6,2
400350be:	4601                	li	a2,0
400350c0:	47dd                	li	a5,23
400350c2:	980592e3          	bnez	a1,40034a46 <tinfl_decompress+0x458>
400350c6:	00961633          	sll	a2,a2,s1
400350ca:	00c9e9b3          	or	s3,s3,a2
400350ce:	04a1                	addi	s1,s1,8
400350d0:	4639                	li	a2,14
400350d2:	fc9673e3          	bgeu	a2,s1,40035098 <tinfl_decompress+0xaaa>
400350d6:	3ff9f613          	andi	a2,s3,1023
400350da:	0b060613          	addi	a2,a2,176
400350de:	0606                	slli	a2,a2,0x1
400350e0:	964a                	add	a2,a2,s2
400350e2:	00061a83          	lh	s5,0(a2)
400350e6:	060acc63          	bltz	s5,4003515e <tinfl_decompress+0xb70>
400350ea:	409ad593          	srai	a1,s5,0x9
400350ee:	1ffafa93          	andi	s5,s5,511
400350f2:	0ff00613          	li	a2,255
400350f6:	00b9d9b3          	srl	s3,s3,a1
400350fa:	8c8d                	sub	s1,s1,a1
400350fc:	15564f63          	blt	a2,s5,4003525a <tinfl_decompress+0xc6c>
40035100:	47b2                	lw	a5,12(sp)
40035102:	08fb7063          	bgeu	s6,a5,40035182 <tinfl_decompress+0xb94>
40035106:	015b0023          	sb	s5,0(s6)
4003510a:	0b05                	addi	s6,s6,1
4003510c:	b491                	j	40034b50 <tinfl_decompress+0x562>
4003510e:	4629                	li	a2,10
40035110:	fa9673e3          	bgeu	a2,s1,400350b6 <tinfl_decompress+0xac8>
40035114:	45a9                	li	a1,10
40035116:	00b9d633          	srl	a2,s3,a1
4003511a:	8a05                	andi	a2,a2,1
4003511c:	40660633          	sub	a2,a2,t1
40035120:	4af60613          	addi	a2,a2,1199
40035124:	0606                	slli	a2,a2,0x1
40035126:	964a                	add	a2,a2,s2
40035128:	00061303          	lh	t1,0(a2)
4003512c:	00158513          	addi	a0,a1,1
40035130:	fa0353e3          	bgez	t1,400350d6 <tinfl_decompress+0xae8>
40035134:	00258613          	addi	a2,a1,2
40035138:	85aa                	mv	a1,a0
4003513a:	fcc4fee3          	bgeu	s1,a2,40035116 <tinfl_decompress+0xb28>
4003513e:	bfa5                	j	400350b6 <tinfl_decompress+0xac8>
40035140:	8b66                	mv	s6,s9
40035142:	8452                	mv	s0,s4
40035144:	bf9d                	j	400350ba <tinfl_decompress+0xacc>
40035146:	ff8a7de3          	bgeu	s4,s8,40035140 <tinfl_decompress+0xb52>
4003514a:	001a0413          	addi	s0,s4,1
4003514e:	000a4603          	lbu	a2,0(s4)
40035152:	8b66                	mv	s6,s9
40035154:	bf8d                	j	400350c6 <tinfl_decompress+0xad8>
40035156:	00044603          	lbu	a2,0(s0)
4003515a:	0405                	addi	s0,s0,1
4003515c:	b7ad                	j	400350c6 <tinfl_decompress+0xad8>
4003515e:	4629                	li	a2,10
40035160:	00160593          	addi	a1,a2,1
40035164:	00c9d633          	srl	a2,s3,a2
40035168:	8a05                	andi	a2,a2,1
4003516a:	41560633          	sub	a2,a2,s5
4003516e:	4af60613          	addi	a2,a2,1199
40035172:	0606                	slli	a2,a2,0x1
40035174:	964a                	add	a2,a2,s2
40035176:	00061a83          	lh	s5,0(a2)
4003517a:	862e                	mv	a2,a1
4003517c:	fe0ac2e3          	bltz	s5,40035160 <tinfl_decompress+0xb72>
40035180:	bf8d                	j	400350f2 <tinfl_decompress+0xb04>
40035182:	47e1                	li	a5,24
40035184:	b055                	j	40034a28 <tinfl_decompress+0x43a>
40035186:	8b66                	mv	s6,s9
40035188:	8452                	mv	s0,s4
4003518a:	bf9d                	j	40035100 <tinfl_decompress+0xb12>
4003518c:	00936e63          	bltu	t1,s1,400351a8 <tinfl_decompress+0xbba>
40035190:	00144603          	lbu	a2,1(s0)
40035194:	00044583          	lbu	a1,0(s0)
40035198:	0409                	addi	s0,s0,2
4003519a:	0622                	slli	a2,a2,0x8
4003519c:	8e4d                	or	a2,a2,a1
4003519e:	00961633          	sll	a2,a2,s1
400351a2:	00c9e9b3          	or	s3,s3,a2
400351a6:	04c1                	addi	s1,s1,16
400351a8:	3ff9f613          	andi	a2,s3,1023
400351ac:	0b060613          	addi	a2,a2,176
400351b0:	0606                	slli	a2,a2,0x1
400351b2:	964a                	add	a2,a2,s2
400351b4:	00061583          	lh	a1,0(a2)
400351b8:	4095d513          	srai	a0,a1,0x9
400351bc:	0205d363          	bgez	a1,400351e2 <tinfl_decompress+0xbf4>
400351c0:	4629                	li	a2,10
400351c2:	00160513          	addi	a0,a2,1
400351c6:	00c9d633          	srl	a2,s3,a2
400351ca:	8a05                	andi	a2,a2,1
400351cc:	40b605b3          	sub	a1,a2,a1
400351d0:	4af58593          	addi	a1,a1,1199
400351d4:	0586                	slli	a1,a1,0x1
400351d6:	95ca                	add	a1,a1,s2
400351d8:	00059583          	lh	a1,0(a1)
400351dc:	862a                	mv	a2,a0
400351de:	fe05c2e3          	bltz	a1,400351c2 <tinfl_decompress+0xbd4>
400351e2:	1005f613          	andi	a2,a1,256
400351e6:	8aae                	mv	s5,a1
400351e8:	00a9d9b3          	srl	s3,s3,a0
400351ec:	8c89                	sub	s1,s1,a0
400351ee:	e635                	bnez	a2,4003525a <tinfl_decompress+0xc6c>
400351f0:	00936e63          	bltu	t1,s1,4003520c <tinfl_decompress+0xc1e>
400351f4:	00144603          	lbu	a2,1(s0)
400351f8:	00044503          	lbu	a0,0(s0)
400351fc:	0409                	addi	s0,s0,2
400351fe:	0622                	slli	a2,a2,0x8
40035200:	8e49                	or	a2,a2,a0
40035202:	00961633          	sll	a2,a2,s1
40035206:	00c9e9b3          	or	s3,s3,a2
4003520a:	04c1                	addi	s1,s1,16
4003520c:	3ff9f613          	andi	a2,s3,1023
40035210:	0b060613          	addi	a2,a2,176
40035214:	0606                	slli	a2,a2,0x1
40035216:	964a                	add	a2,a2,s2
40035218:	00061f03          	lh	t5,0(a2)
4003521c:	409f5513          	srai	a0,t5,0x9
40035220:	020f5363          	bgez	t5,40035246 <tinfl_decompress+0xc58>
40035224:	4629                	li	a2,10
40035226:	00160513          	addi	a0,a2,1
4003522a:	00c9d633          	srl	a2,s3,a2
4003522e:	8a05                	andi	a2,a2,1
40035230:	41e60633          	sub	a2,a2,t5
40035234:	4af60613          	addi	a2,a2,1199
40035238:	0606                	slli	a2,a2,0x1
4003523a:	964a                	add	a2,a2,s2
4003523c:	00061f03          	lh	t5,0(a2)
40035240:	862a                	mv	a2,a0
40035242:	fe0f42e3          	bltz	t5,40035226 <tinfl_decompress+0xc38>
40035246:	00bb0023          	sb	a1,0(s6)
4003524a:	100f7613          	andi	a2,t5,256
4003524e:	00a9d9b3          	srl	s3,s3,a0
40035252:	8c89                	sub	s1,s1,a0
40035254:	ce29                	beqz	a2,400352ae <tinfl_decompress+0xcc0>
40035256:	0b05                	addi	s6,s6,1
40035258:	8afa                	mv	s5,t5
4003525a:	1ffafa93          	andi	s5,s5,511
4003525e:	10000613          	li	a2,256
40035262:	82ca88e3          	beq	s5,a2,40034a92 <tinfl_decompress+0x4a4>
40035266:	effa8a93          	addi	s5,s5,-257
4003526a:	3ff1d6b7          	lui	a3,0x3ff1d
4003526e:	002a9613          	slli	a2,s5,0x2
40035272:	2b468693          	addi	a3,a3,692 # 3ff1d2b4 <s_length_extra.2680>
40035276:	96b2                	add	a3,a3,a2
40035278:	3ff1dab7          	lui	s5,0x3ff1d
4003527c:	0006ad03          	lw	s10,0(a3)
40035280:	224a8a93          	addi	s5,s5,548 # 3ff1d224 <s_length_base.2679>
40035284:	9ab2                	add	s5,s5,a2
40035286:	000aaa83          	lw	s5,0(s5)
4003528a:	060d0063          	beqz	s10,400352ea <tinfl_decompress+0xcfc>
4003528e:	05a4f363          	bgeu	s1,s10,400352d4 <tinfl_decompress+0xce6>
40035292:	03846d63          	bltu	s0,s8,400352cc <tinfl_decompress+0xcde>
40035296:	00287593          	andi	a1,a6,2
4003529a:	4601                	li	a2,0
4003529c:	47e5                	li	a5,25
4003529e:	fa059463          	bnez	a1,40034a46 <tinfl_decompress+0x458>
400352a2:	00961633          	sll	a2,a2,s1
400352a6:	00c9e9b3          	or	s3,s3,a2
400352aa:	04a1                	addi	s1,s1,8
400352ac:	b7cd                	j	4003528e <tinfl_decompress+0xca0>
400352ae:	01eb00a3          	sb	t5,1(s6)
400352b2:	0b09                	addi	s6,s6,2
400352b4:	b04d                	j	40034b56 <tinfl_decompress+0x568>
400352b6:	8b66                	mv	s6,s9
400352b8:	8452                	mv	s0,s4
400352ba:	bff1                	j	40035296 <tinfl_decompress+0xca8>
400352bc:	ff8a7de3          	bgeu	s4,s8,400352b6 <tinfl_decompress+0xcc8>
400352c0:	001a0413          	addi	s0,s4,1
400352c4:	000a4603          	lbu	a2,0(s4)
400352c8:	8b66                	mv	s6,s9
400352ca:	bfe1                	j	400352a2 <tinfl_decompress+0xcb4>
400352cc:	00044603          	lbu	a2,0(s0)
400352d0:	0405                	addi	s0,s0,1
400352d2:	bfc1                	j	400352a2 <tinfl_decompress+0xcb4>
400352d4:	4605                	li	a2,1
400352d6:	01a61633          	sll	a2,a2,s10
400352da:	167d                	addi	a2,a2,-1
400352dc:	01367633          	and	a2,a2,s3
400352e0:	41a484b3          	sub	s1,s1,s10
400352e4:	01a9d9b3          	srl	s3,s3,s10
400352e8:	9ab2                	add	s5,s5,a2
400352ea:	4639                	li	a2,14
400352ec:	04966763          	bltu	a2,s1,4003533a <tinfl_decompress+0xd4c>
400352f0:	408c0633          	sub	a2,s8,s0
400352f4:	4585                	li	a1,1
400352f6:	0ec5cf63          	blt	a1,a2,400353f4 <tinfl_decompress+0xe06>
400352fa:	3ff9f613          	andi	a2,s3,1023
400352fe:	78060613          	addi	a2,a2,1920
40035302:	0606                	slli	a2,a2,0x1
40035304:	964a                	add	a2,a2,s2
40035306:	00061e03          	lh	t3,0(a2)
4003530a:	080e4a63          	bltz	t3,4003539e <tinfl_decompress+0xdb0>
4003530e:	409e5e13          	srai	t3,t3,0x9
40035312:	000e0463          	beqz	t3,4003531a <tinfl_decompress+0xd2c>
40035316:	03c4f263          	bgeu	s1,t3,4003533a <tinfl_decompress+0xd4c>
4003531a:	0d846963          	bltu	s0,s8,400353ec <tinfl_decompress+0xdfe>
4003531e:	00287593          	andi	a1,a6,2
40035322:	4601                	li	a2,0
40035324:	47e9                	li	a5,26
40035326:	f2059063          	bnez	a1,40034a46 <tinfl_decompress+0x458>
4003532a:	00961633          	sll	a2,a2,s1
4003532e:	00c9e9b3          	or	s3,s3,a2
40035332:	04a1                	addi	s1,s1,8
40035334:	4639                	li	a2,14
40035336:	fc9672e3          	bgeu	a2,s1,400352fa <tinfl_decompress+0xd0c>
4003533a:	3ff9f693          	andi	a3,s3,1023
4003533e:	78068693          	addi	a3,a3,1920
40035342:	0686                	slli	a3,a3,0x1
40035344:	96ca                	add	a3,a3,s2
40035346:	00069603          	lh	a2,0(a3)
4003534a:	0c064563          	bltz	a2,40035414 <tinfl_decompress+0xe26>
4003534e:	40965593          	srai	a1,a2,0x9
40035352:	1ff67613          	andi	a2,a2,511
40035356:	3ff1d6b7          	lui	a3,0x3ff1d
4003535a:	060a                	slli	a2,a2,0x2
4003535c:	1a468693          	addi	a3,a3,420 # 3ff1d1a4 <s_dist_extra.2682>
40035360:	96b2                	add	a3,a3,a2
40035362:	00b9d9b3          	srl	s3,s3,a1
40035366:	8c8d                	sub	s1,s1,a1
40035368:	0006ad03          	lw	s10,0(a3)
4003536c:	3ff1d5b7          	lui	a1,0x3ff1d
40035370:	12458593          	addi	a1,a1,292 # 3ff1d124 <s_dist_base.2681>
40035374:	962e                	add	a2,a2,a1
40035376:	00062d83          	lw	s11,0(a2)
4003537a:	0e0d0c63          	beqz	s10,40035472 <tinfl_decompress+0xe84>
4003537e:	0da4ff63          	bgeu	s1,s10,4003545c <tinfl_decompress+0xe6e>
40035382:	0d846963          	bltu	s0,s8,40035454 <tinfl_decompress+0xe66>
40035386:	00287593          	andi	a1,a6,2
4003538a:	4601                	li	a2,0
4003538c:	47ed                	li	a5,27
4003538e:	ea059c63          	bnez	a1,40034a46 <tinfl_decompress+0x458>
40035392:	00961633          	sll	a2,a2,s1
40035396:	00c9e9b3          	or	s3,s3,a2
4003539a:	04a1                	addi	s1,s1,8
4003539c:	b7cd                	j	4003537e <tinfl_decompress+0xd90>
4003539e:	4629                	li	a2,10
400353a0:	f6967de3          	bgeu	a2,s1,4003531a <tinfl_decompress+0xd2c>
400353a4:	6505                	lui	a0,0x1
400353a6:	45a9                	li	a1,10
400353a8:	b8050513          	addi	a0,a0,-1152 # b80 <RvExcFrameSize+0xaf0>
400353ac:	00b9d633          	srl	a2,s3,a1
400353b0:	fffe4e13          	not	t3,t3
400353b4:	8a05                	andi	a2,a2,1
400353b6:	9672                	add	a2,a2,t3
400353b8:	962a                	add	a2,a2,a0
400353ba:	0606                	slli	a2,a2,0x1
400353bc:	964a                	add	a2,a2,s2
400353be:	00061e03          	lh	t3,0(a2)
400353c2:	00158313          	addi	t1,a1,1
400353c6:	f60e5ae3          	bgez	t3,4003533a <tinfl_decompress+0xd4c>
400353ca:	00258613          	addi	a2,a1,2
400353ce:	859a                	mv	a1,t1
400353d0:	fcc4fee3          	bgeu	s1,a2,400353ac <tinfl_decompress+0xdbe>
400353d4:	b799                	j	4003531a <tinfl_decompress+0xd2c>
400353d6:	8b66                	mv	s6,s9
400353d8:	8452                	mv	s0,s4
400353da:	b791                	j	4003531e <tinfl_decompress+0xd30>
400353dc:	ff8a7de3          	bgeu	s4,s8,400353d6 <tinfl_decompress+0xde8>
400353e0:	001a0413          	addi	s0,s4,1
400353e4:	000a4603          	lbu	a2,0(s4)
400353e8:	8b66                	mv	s6,s9
400353ea:	b781                	j	4003532a <tinfl_decompress+0xd3c>
400353ec:	00044603          	lbu	a2,0(s0)
400353f0:	0405                	addi	s0,s0,1
400353f2:	bf25                	j	4003532a <tinfl_decompress+0xd3c>
400353f4:	00144683          	lbu	a3,1(s0)
400353f8:	00848613          	addi	a2,s1,8
400353fc:	0409                	addi	s0,s0,2
400353fe:	00c696b3          	sll	a3,a3,a2
40035402:	ffe44603          	lbu	a2,-2(s0)
40035406:	00961633          	sll	a2,a2,s1
4003540a:	8ed1                	or	a3,a3,a2
4003540c:	00d9e9b3          	or	s3,s3,a3
40035410:	04c1                	addi	s1,s1,16
40035412:	b725                	j	4003533a <tinfl_decompress+0xd4c>
40035414:	6505                	lui	a0,0x1
40035416:	46a9                	li	a3,10
40035418:	b8050513          	addi	a0,a0,-1152 # b80 <RvExcFrameSize+0xaf0>
4003541c:	00168593          	addi	a1,a3,1
40035420:	00d9d6b3          	srl	a3,s3,a3
40035424:	fff64613          	not	a2,a2
40035428:	8a85                	andi	a3,a3,1
4003542a:	96b2                	add	a3,a3,a2
4003542c:	96aa                	add	a3,a3,a0
4003542e:	0686                	slli	a3,a3,0x1
40035430:	96ca                	add	a3,a3,s2
40035432:	00069603          	lh	a2,0(a3)
40035436:	86ae                	mv	a3,a1
40035438:	fe0642e3          	bltz	a2,4003541c <tinfl_decompress+0xe2e>
4003543c:	bf29                	j	40035356 <tinfl_decompress+0xd68>
4003543e:	8b66                	mv	s6,s9
40035440:	8452                	mv	s0,s4
40035442:	b791                	j	40035386 <tinfl_decompress+0xd98>
40035444:	ff8a7de3          	bgeu	s4,s8,4003543e <tinfl_decompress+0xe50>
40035448:	001a0413          	addi	s0,s4,1
4003544c:	000a4603          	lbu	a2,0(s4)
40035450:	8b66                	mv	s6,s9
40035452:	b781                	j	40035392 <tinfl_decompress+0xda4>
40035454:	00044603          	lbu	a2,0(s0)
40035458:	0405                	addi	s0,s0,1
4003545a:	bf25                	j	40035392 <tinfl_decompress+0xda4>
4003545c:	4605                	li	a2,1
4003545e:	01a61633          	sll	a2,a2,s10
40035462:	167d                	addi	a2,a2,-1
40035464:	01367633          	and	a2,a2,s3
40035468:	41a484b3          	sub	s1,s1,s10
4003546c:	01a9d9b3          	srl	s3,s3,s10
40035470:	9db2                	add	s11,s11,a2
40035472:	47c2                	lw	a5,16(sp)
40035474:	40fb07b3          	sub	a5,s6,a5
40035478:	c43e                	sw	a5,8(sp)
4003547a:	01b7fb63          	bgeu	a5,s11,40035490 <tinfl_decompress+0xea2>
4003547e:	47f2                	lw	a5,28(sp)
40035480:	cb81                	beqz	a5,40035490 <tinfl_decompress+0xea2>
40035482:	02500793          	li	a5,37
40035486:	cdaff06f          	j	40034960 <tinfl_decompress+0x372>
4003548a:	8b66                	mv	s6,s9
4003548c:	8452                	mv	s0,s4
4003548e:	bfd5                	j	40035482 <tinfl_decompress+0xe94>
40035490:	47a2                	lw	a5,8(sp)
40035492:	85da                	mv	a1,s6
40035494:	41b78633          	sub	a2,a5,s11
40035498:	47c2                	lw	a5,16(sp)
4003549a:	01767633          	and	a2,a2,s7
4003549e:	963e                	add	a2,a2,a5
400354a0:	00cb7363          	bgeu	s6,a2,400354a6 <tinfl_decompress+0xeb8>
400354a4:	85b2                	mv	a1,a2
400354a6:	47b2                	lw	a5,12(sp)
400354a8:	95d6                	add	a1,a1,s5
400354aa:	06b7ee63          	bltu	a5,a1,40035526 <tinfl_decompress+0xf38>
400354ae:	835a                	mv	t1,s6
400354b0:	8556                	mv	a0,s5
400354b2:	4589                	li	a1,2
400354b4:	00064e03          	lbu	t3,0(a2)
400354b8:	1af5                	addi	s5,s5,-3
400354ba:	0b0d                	addi	s6,s6,3
400354bc:	ffcb0ea3          	sb	t3,-3(s6)
400354c0:	00164e03          	lbu	t3,1(a2)
400354c4:	060d                	addi	a2,a2,3
400354c6:	ffcb0f23          	sb	t3,-2(s6)
400354ca:	fff64e03          	lbu	t3,-1(a2)
400354ce:	ffcb0fa3          	sb	t3,-1(s6)
400354d2:	0755c163          	blt	a1,s5,40035534 <tinfl_decompress+0xf46>
400354d6:	e7505d63          	blez	s5,40034b50 <tinfl_decompress+0x562>
400354da:	00064e03          	lbu	t3,0(a2)
400354de:	01cb0023          	sb	t3,0(s6)
400354e2:	00ba9663          	bne	s5,a1,400354ee <tinfl_decompress+0xf00>
400354e6:	00164603          	lbu	a2,1(a2)
400354ea:	00cb00a3          	sb	a2,1(s6)
400354ee:	00a30b33          	add	s6,t1,a0
400354f2:	e5eff06f          	j	40034b50 <tinfl_decompress+0x562>
400354f6:	03500793          	li	a5,53
400354fa:	d2eff06f          	j	40034a28 <tinfl_decompress+0x43a>
400354fe:	8b66                	mv	s6,s9
40035500:	8452                	mv	s0,s4
40035502:	47b2                	lw	a5,12(sp)
40035504:	fefb79e3          	bgeu	s6,a5,400354f6 <tinfl_decompress+0xf08>
40035508:	47a2                	lw	a5,8(sp)
4003550a:	0b05                	addi	s6,s6,1
4003550c:	41b78633          	sub	a2,a5,s11
40035510:	47c2                	lw	a5,16(sp)
40035512:	01767633          	and	a2,a2,s7
40035516:	963e                	add	a2,a2,a5
40035518:	47a2                	lw	a5,8(sp)
4003551a:	00064603          	lbu	a2,0(a2)
4003551e:	0785                	addi	a5,a5,1
40035520:	fecb0fa3          	sb	a2,-1(s6)
40035524:	c43e                	sw	a5,8(sp)
40035526:	8656                	mv	a2,s5
40035528:	5afd                	li	s5,-1
4003552a:	e2060363          	beqz	a2,40034b50 <tinfl_decompress+0x562>
4003552e:	fff60a93          	addi	s5,a2,-1
40035532:	bfc1                	j	40035502 <tinfl_decompress+0xf14>
40035534:	835a                	mv	t1,s6
40035536:	8556                	mv	a0,s5
40035538:	bfb5                	j	400354b4 <tinfl_decompress+0xec6>
4003553a:	8b66                	mv	s6,s9
4003553c:	8452                	mv	s0,s4
4003553e:	d72ff06f          	j	40034ab0 <tinfl_decompress+0x4c2>
40035542:	ff8a7ce3          	bgeu	s4,s8,4003553a <tinfl_decompress+0xf4c>
40035546:	001a0413          	addi	s0,s4,1
4003554a:	000a4603          	lbu	a2,0(s4)
4003554e:	8b66                	mv	s6,s9
40035550:	d6cff06f          	j	40034abc <tinfl_decompress+0x4ce>
40035554:	00044603          	lbu	a2,0(s0)
40035558:	0405                	addi	s0,s0,1
4003555a:	d62ff06f          	j	40034abc <tinfl_decompress+0x4ce>
4003555e:	0074f613          	andi	a2,s1,7
40035562:	00c9d9b3          	srl	s3,s3,a2
40035566:	98e1                	andi	s1,s1,-8
40035568:	4a81                	li	s5,0
4003556a:	c8a5                	beqz	s1,400355da <tinfl_decompress+0xfec>
4003556c:	461d                	li	a2,7
4003556e:	04966063          	bltu	a2,s1,400355ae <tinfl_decompress+0xfc0>
40035572:	03846a63          	bltu	s0,s8,400355a6 <tinfl_decompress+0xfb8>
40035576:	00287593          	andi	a1,a6,2
4003557a:	4601                	li	a2,0
4003557c:	02900793          	li	a5,41
40035580:	cc059363          	bnez	a1,40034a46 <tinfl_decompress+0x458>
40035584:	00961633          	sll	a2,a2,s1
40035588:	00c9e9b3          	or	s3,s3,a2
4003558c:	04a1                	addi	s1,s1,8
4003558e:	bff9                	j	4003556c <tinfl_decompress+0xf7e>
40035590:	8b66                	mv	s6,s9
40035592:	8452                	mv	s0,s4
40035594:	b7cd                	j	40035576 <tinfl_decompress+0xf88>
40035596:	ff8a7de3          	bgeu	s4,s8,40035590 <tinfl_decompress+0xfa2>
4003559a:	001a0413          	addi	s0,s4,1
4003559e:	000a4603          	lbu	a2,0(s4)
400355a2:	8b66                	mv	s6,s9
400355a4:	b7c5                	j	40035584 <tinfl_decompress+0xf96>
400355a6:	00044603          	lbu	a2,0(s0)
400355aa:	0405                	addi	s0,s0,1
400355ac:	bfe1                	j	40035584 <tinfl_decompress+0xf96>
400355ae:	0ff9f593          	zext.b	a1,s3
400355b2:	14e1                	addi	s1,s1,-8
400355b4:	0089d993          	srli	s3,s3,0x8
400355b8:	01092603          	lw	a2,16(s2)
400355bc:	0a85                	addi	s5,s5,1
400355be:	0622                	slli	a2,a2,0x8
400355c0:	8e4d                	or	a2,a2,a1
400355c2:	00c92823          	sw	a2,16(s2)
400355c6:	460d                	li	a2,3
400355c8:	fb5671e3          	bgeu	a2,s5,4003556a <tinfl_decompress+0xf7c>
400355cc:	02200793          	li	a5,34
400355d0:	00f92023          	sw	a5,0(s2)
400355d4:	4501                	li	a0,0
400355d6:	910ff06f          	j	400346e6 <tinfl_decompress+0xf8>
400355da:	03846563          	bltu	s0,s8,40035604 <tinfl_decompress+0x1016>
400355de:	00287613          	andi	a2,a6,2
400355e2:	4581                	li	a1,0
400355e4:	02a00793          	li	a5,42
400355e8:	da61                	beqz	a2,400355b8 <tinfl_decompress+0xfca>
400355ea:	c5cff06f          	j	40034a46 <tinfl_decompress+0x458>
400355ee:	8b66                	mv	s6,s9
400355f0:	8452                	mv	s0,s4
400355f2:	b7f5                	j	400355de <tinfl_decompress+0xff0>
400355f4:	ff8a7de3          	bgeu	s4,s8,400355ee <tinfl_decompress+0x1000>
400355f8:	001a0413          	addi	s0,s4,1
400355fc:	000a4583          	lbu	a1,0(s4)
40035600:	8b66                	mv	s6,s9
40035602:	bf5d                	j	400355b8 <tinfl_decompress+0xfca>
40035604:	00044583          	lbu	a1,0(s0)
40035608:	0405                	addi	s0,s0,1
4003560a:	b77d                	j	400355b8 <tinfl_decompress+0xfca>
4003560c:	8b66                	mv	s6,s9
4003560e:	8452                	mv	s0,s4
40035610:	bf75                	j	400355cc <tinfl_decompress+0xfde>
40035612:	8b66                	mv	s6,s9
40035614:	8452                	mv	s0,s4
40035616:	a12ff06f          	j	40034828 <tinfl_decompress+0x23a>
4003561a:	0005c783          	lbu	a5,0(a1)
4003561e:	05a1                	addi	a1,a1,8
40035620:	97fe                	add	a5,a5,t6
40035622:	ff95cf83          	lbu	t6,-7(a1)
40035626:	9fbe                	add	t6,t6,a5
40035628:	01f786b3          	add	a3,a5,t6
4003562c:	ffa5c783          	lbu	a5,-6(a1)
40035630:	96b2                	add	a3,a3,a2
40035632:	ffb5c603          	lbu	a2,-5(a1)
40035636:	97fe                	add	a5,a5,t6
40035638:	96be                	add	a3,a3,a5
4003563a:	97b2                	add	a5,a5,a2
4003563c:	ffc5c603          	lbu	a2,-4(a1)
40035640:	96be                	add	a3,a3,a5
40035642:	fff5cf83          	lbu	t6,-1(a1)
40035646:	963e                	add	a2,a2,a5
40035648:	ffd5c783          	lbu	a5,-3(a1)
4003564c:	96b2                	add	a3,a3,a2
4003564e:	963e                	add	a2,a2,a5
40035650:	ffe5c783          	lbu	a5,-2(a1)
40035654:	96b2                	add	a3,a3,a2
40035656:	97b2                	add	a5,a5,a2
40035658:	96be                	add	a3,a3,a5
4003565a:	9fbe                	add	t6,t6,a5
4003565c:	01f68633          	add	a2,a3,t6
40035660:	01e587b3          	add	a5,a1,t5
40035664:	fb17ebe3          	bltu	a5,a7,4003561a <tinfl_decompress+0x102c>
40035668:	0038df13          	srli	t5,a7,0x3
4003566c:	0f0e                	slli	t5,t5,0x3
4003566e:	ff88f593          	andi	a1,a7,-8
40035672:	9cfa                	add	s9,s9,t5
40035674:	419585b3          	sub	a1,a1,s9
40035678:	00bc87b3          	add	a5,s9,a1
4003567c:	0117ef63          	bltu	a5,a7,4003569a <tinfl_decompress+0x10ac>
40035680:	411b0b33          	sub	s6,s6,a7
40035684:	03cfffb3          	remu	t6,t6,t3
40035688:	889a                	mv	a7,t1
4003568a:	03c67633          	remu	a2,a2,t3
4003568e:	8b0ff06f          	j	4003473e <tinfl_decompress+0x150>
40035692:	85e6                	mv	a1,s9
40035694:	419e8f33          	sub	t5,t4,s9
40035698:	b7e1                	j	40035660 <tinfl_decompress+0x1072>
4003569a:	0c85                	addi	s9,s9,1
4003569c:	fffcc783          	lbu	a5,-1(s9)
400356a0:	9fbe                	add	t6,t6,a5
400356a2:	967e                	add	a2,a2,t6
400356a4:	bfd1                	j	40035678 <tinfl_decompress+0x108a>
