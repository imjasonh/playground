
40048944 <ets_rsa_pss_verify>:
40048944:	ce010113          	addi	x2,x2,-800
40048948:	30812c23          	sw	x8,792(x2)
4004894c:	30912a23          	sw	x9,788(x2)
40048950:	842a                	mv	x8,x10
40048952:	31312623          	sw	x19,780(x2)
40048956:	84b2                	mv	x9,x12
40048958:	89ae                	mv	x19,x11
4004895a:	18000613          	li	x12,384
4004895e:	4581                	li	x11,0
40048960:	0308                	addi	x10,x2,384
40048962:	30112e23          	sw	x1,796(x2)
40048966:	31212823          	sw	x18,784(x2)
4004896a:	8936                	mv	x18,x13
4004896c:	7730f0ef          	jal	400588de <memset>
40048970:	4611                	li	x12,4
40048972:	18040593          	addi	x11,x8,384
40048976:	0308                	addi	x10,x2,384
40048978:	6430f0ef          	jal	400587ba <memcpy>
4004897c:	827fd0ef          	jal	400461a2 <ets_bigint_enable>
40048980:	30442683          	lw	x13,772(x8)
40048984:	06000813          	li	x16,96
40048988:	4781                	li	x15,0
4004898a:	18440713          	addi	x14,x8,388
4004898e:	8622                	mv	x12,x8
40048990:	030c                	addi	x11,x2,384
40048992:	854e                	mv	x10,x19
40048994:	8ddfd0ef          	jal	40046270 <ets_bigint_modexp>
40048998:	cd11                	beqz	x10,400489b4 <ets_rsa_pss_verify+0x70>
4004899a:	3ff1c5b7          	lui	x11,0x3ff1c
4004899e:	3ff1b537          	lui	x10,0x3ff1b
400489a2:	02c00613          	li	x12,44
400489a6:	b7058593          	addi	x11,x11,-1168 # 3ff1bb70 <usb_data_stuff+0x58>
400489aa:	7ec50513          	addi	x10,x10,2028 # 3ff1b7ec <CSWTCH.11+0x34>
400489ae:	d27ff0ef          	jal	400486d4 <ets_printf>
400489b2:	a001                	j	400489b2 <ets_rsa_pss_verify+0x6e>
400489b4:	8d5fd0ef          	jal	40046288 <ets_bigint_wait_finish>
400489b8:	06000593          	li	x11,96
400489bc:	850a                	mv	x10,x2
400489be:	8dffd0ef          	jal	4004629c <ets_bigint_getz>
400489c2:	cd11                	beqz	x10,400489de <ets_rsa_pss_verify+0x9a>
400489c4:	3ff1c5b7          	lui	x11,0x3ff1c
400489c8:	3ff1b537          	lui	x10,0x3ff1b
400489cc:	02f00613          	li	x12,47
400489d0:	b7058593          	addi	x11,x11,-1168 # 3ff1bb70 <usb_data_stuff+0x58>
400489d4:	7ec50513          	addi	x10,x10,2028 # 3ff1b7ec <CSWTCH.11+0x34>
400489d8:	cfdff0ef          	jal	400486d4 <ets_printf>
400489dc:	a001                	j	400489dc <ets_rsa_pss_verify+0x98>
400489de:	fecfd0ef          	jal	400461ca <ets_bigint_disable>
400489e2:	878a                	mv	x15,x2
400489e4:	f4010693          	addi	x13,x2,-192
400489e8:	870a                	mv	x14,x2
400489ea:	00074583          	lbu	x11,0(x14)
400489ee:	17f7c603          	lbu	x12,383(x15)
400489f2:	17fd                	addi	x15,x15,-1
400489f4:	18b78023          	sb	x11,384(x15)
400489f8:	00c70023          	sb	x12,0(x14)
400489fc:	0705                	addi	x14,x14,1
400489fe:	fed796e3          	bne	x15,x13,400489ea <ets_rsa_pss_verify+0xa6>
40048a02:	864a                	mv	x12,x18
40048a04:	85a6                	mv	x11,x9
40048a06:	850a                	mv	x10,x2
40048a08:	dedff0ef          	jal	400487f4 <ets_emsa_pss_verify>
40048a0c:	31c12083          	lw	x1,796(x2)
40048a10:	31812403          	lw	x8,792(x2)
40048a14:	31412483          	lw	x9,788(x2)
40048a18:	31012903          	lw	x18,784(x2)
40048a1c:	30c12983          	lw	x19,780(x2)
40048a20:	32010113          	addi	x2,x2,800
40048a24:	8082                	ret
