import C3BootProofs.Proofs.ScalarMontFacts

/-! # `montgomery_mul`'s values, part 2

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-scalar-mont.py` writes this file. -/

namespace C3.RV32

open C3.Image

theorem smm_v_PN4L2 {v470 v607 v640 : Word}
    (t607 : v607.toNat = v470.toNat * 501691798 % 2 ^ 32)
    (t640 : v640.toNat = v470.toNat * 501691798 / 2 ^ 32) :
    v607.toNat + 2 ^ 32 * v640.toNat = v470.toNat * 501691798 := by
  have := v470.isLt; have := v607.isLt; have := v640.isLt
  generalize v470.toNat = n470 at *
  generalize v607.toNat = n607 at *
  generalize v640.toNat = n640 at *
  omega

theorem smm_v_PN5L1 {v523 v615 v644 : Word}
    (t615 : v615.toNat = v523.toNat * 9640146 % 2 ^ 32)
    (t644 : v644.toNat = v523.toNat * 9640146 / 2 ^ 32) :
    v615.toNat + 2 ^ 32 * v644.toNat = v523.toNat * 9640146 := by
  have := v523.isLt; have := v615.isLt; have := v644.isLt
  generalize v523.toNat = n523 at *
  generalize v615.toNat = n615 at *
  generalize v644.toNat = n644 at *
  omega

theorem smm_v_S6 {v528 v530 v533 v539 v542 v544 v546 v548 v550 v553 v554 v603 v607 v615 v626 v627 v634 v635 v640 v644 v650 v655 v656 v657 v659 v660 v667 v669 v670 v672 v673 v674 : Word}
    (t544 : v544.toNat = (v528.toNat + v539.toNat) % 2 ^ 32)
    (t548 : v546.toNat + 2 ^ 32 * v548.toNat = v530.toNat + v533.toNat)
    (t550 : v550.toNat = (v548.toNat + v544.toNat) % 2 ^ 32)
    (t554 : v554.toNat = (v550.toNat + v542.toNat) % 2 ^ 32)
    (t650 : v626.toNat + 2 ^ 32 * v650.toNat = v603.toNat + v546.toNat)
    (t655 : v655.toNat = (v554.toNat + v650.toNat) % 2 ^ 32)
    (t656 : v656.toNat = (v640.toNat + v655.toNat) % 2 ^ 32)
    (t657 : v627.toNat + 2 ^ 32 * v657.toNat = v626.toNat + v607.toNat)
    (t659 : v659.toNat = (v657.toNat + v656.toNat) % 2 ^ 32)
    (t660 : v660.toNat = (v659.toNat + v644.toNat) % 2 ^ 32)
    (t667 : v634.toNat + 2 ^ 32 * v667.toNat = v615.toNat + v627.toNat)
    (t669 : v669.toNat = (v660.toNat + v667.toNat) % 2 ^ 32)
    (t672 : v672.toNat = (v670.toNat + v669.toNat) % 2 ^ 32)
    (t673 : v635.toNat + 2 ^ 32 * v673.toNat = v634.toNat + v553.toNat)
    (t674 : v674.toNat = (v672.toNat + v673.toNat) % 2 ^ 32) :
    v635.toNat + 2 ^ 32 * v674.toNat = ((v553.toNat + 2 ^ 32 * v670.toNat) + (v533.toNat + 2 ^ 32 * v539.toNat) + (v530.toNat + 2 ^ 32 * v528.toNat) + (v603.toNat + 2 ^ 32 * v542.toNat) + (v607.toNat + 2 ^ 32 * v640.toNat) + (v615.toNat + 2 ^ 32 * v644.toNat)) % 2 ^ 64 := by
  obtain ⟨q544, eq544⟩ := mod_q t544; clear t544
  obtain ⟨q550, eq550⟩ := mod_q t550; clear t550
  obtain ⟨q554, eq554⟩ := mod_q t554; clear t554
  obtain ⟨q655, eq655⟩ := mod_q t655; clear t655
  obtain ⟨q656, eq656⟩ := mod_q t656; clear t656
  obtain ⟨q659, eq659⟩ := mod_q t659; clear t659
  obtain ⟨q660, eq660⟩ := mod_q t660; clear t660
  obtain ⟨q669, eq669⟩ := mod_q t669; clear t669
  obtain ⟨q672, eq672⟩ := mod_q t672; clear t672
  obtain ⟨q674, eq674⟩ := mod_q t674; clear t674
  have key : v635.toNat + 2 ^ 32 * v674.toNat + 2 ^ 64 * (q544 + q550 + q554 + q655 + q656 + q659 + q660 + q669 + q672 + q674) = ((v553.toNat + 2 ^ 32 * v670.toNat) + (v533.toNat + 2 ^ 32 * v539.toNat) + (v530.toNat + 2 ^ 32 * v528.toNat) + (v603.toNat + 2 ^ 32 * v542.toNat) + (v607.toNat + 2 ^ 32 * v640.toNat) + (v615.toNat + 2 ^ 32 * v644.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v528.toNat = n528 at *
    generalize v530.toNat = n530 at *
    generalize v533.toNat = n533 at *
    generalize v539.toNat = n539 at *
    generalize v542.toNat = n542 at *
    generalize v544.toNat = n544 at *
    generalize v546.toNat = n546 at *
    generalize v548.toNat = n548 at *
    generalize v550.toNat = n550 at *
    generalize v553.toNat = n553 at *
    generalize v554.toNat = n554 at *
    generalize v603.toNat = n603 at *
    generalize v607.toNat = n607 at *
    generalize v615.toNat = n615 at *
    generalize v626.toNat = n626 at *
    generalize v627.toNat = n627 at *
    generalize v634.toNat = n634 at *
    generalize v635.toNat = n635 at *
    generalize v640.toNat = n640 at *
    generalize v644.toNat = n644 at *
    generalize v650.toNat = n650 at *
    generalize v655.toNat = n655 at *
    generalize v656.toNat = n656 at *
    generalize v657.toNat = n657 at *
    generalize v659.toNat = n659 at *
    generalize v660.toNat = n660 at *
    generalize v667.toNat = n667 at *
    generalize v669.toNat = n669 at *
    generalize v670.toNat = n670 at *
    generalize v672.toNat = n672 at *
    generalize v673.toNat = n673 at *
    generalize v674.toNat = n674 at *
    omega
  exact smm_key key (smm_lt v635 v674)

theorem smm_v_N6 {v635 v645 v662 v674 : Word}
    (t645 : v645.toNat = v635.toNat * 307527195 % 2 ^ 32)
    (t662 : v662.toNat = v645.toNat % 2 ^ 29) :
    v662.toNat = ((v635.toNat + 2 ^ 32 * v674.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v635.isLt; have := v645.isLt; have := v662.isLt; have := v674.isLt
  generalize v635.toNat = n635 at *
  generalize v645.toNat = n645 at *
  generalize v662.toNat = n662 at *
  generalize v674.toNat = n674 at *
  omega

theorem smm_v_PN6L0 {v662 v665 v671 : Word}
    (t665 : v665.toNat = v662.toNat * 485872621 / 2 ^ 32)
    (t671 : v671.toNat = v662.toNat * 485872621 % 2 ^ 32) :
    v671.toNat + 2 ^ 32 * v665.toNat = v662.toNat * 485872621 := by
  have := v662.isLt; have := v665.isLt; have := v671.isLt
  generalize v662.toNat = n662 at *
  generalize v665.toNat = n665 at *
  generalize v671.toNat = n671 at *
  omega

theorem smm_v_T6 {v635 v665 v671 v674 v677 v687 v691 v692 : Word}
    (t677 : v677.toNat = (v674.toNat + v665.toNat) % 2 ^ 32)
    (t691 : v687.toNat + 2 ^ 32 * v691.toNat = v635.toNat + v671.toNat)
    (t692 : v692.toNat = (v677.toNat + v691.toNat) % 2 ^ 32) :
    v687.toNat + 2 ^ 32 * v692.toNat = ((v635.toNat + 2 ^ 32 * v674.toNat) + (v671.toNat + 2 ^ 32 * v665.toNat)) % 2 ^ 64 := by
  obtain ⟨q677, eq677⟩ := mod_q t677; clear t677
  obtain ⟨q692, eq692⟩ := mod_q t692; clear t692
  have key : v687.toNat + 2 ^ 32 * v692.toNat + 2 ^ 64 * (q677 + q692) = ((v635.toNat + 2 ^ 32 * v674.toNat) + (v671.toNat + 2 ^ 32 * v665.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v635.toNat = n635 at *
    generalize v665.toNat = n665 at *
    generalize v671.toNat = n671 at *
    generalize v674.toNat = n674 at *
    generalize v677.toNat = n677 at *
    generalize v687.toNat = n687 at *
    generalize v691.toNat = n691 at *
    generalize v692.toNat = n692 at *
    omega
  exact smm_key key (smm_lt v687 v692)

theorem smm_v_C6 {v687 v692 v717 v720 v721 v745 : Word}
    (t717 : v717.toNat = v687.toNat / 2 ^ 29)
    (t720 : v720.toNat = v692.toNat * 2 ^ 3 % 2 ^ 32)
    (t721 : v721.toNat = v717.toNat + v720.toNat)
    (t745 : v745.toNat = v692.toNat / 2 ^ 29) :
    v721.toNat + 2 ^ 32 * v745.toNat = (v687.toNat + 2 ^ 32 * v692.toNat) / 2 ^ 29 := by
  have := v687.isLt; have := v692.isLt; have := v717.isLt; have := v720.isLt; have := v721.isLt; have := v745.isLt
  generalize v687.toNat = n687 at *
  generalize v692.toNat = n692 at *
  generalize v717.toNat = n717 at *
  generalize v720.toNat = n720 at *
  generalize v721.toNat = n721 at *
  generalize v745.toNat = n745 at *
  omega

theorem smm_v_PN3L4 {v401 v697 v699 : Word}
    (t697 : v697.toNat = v401.toNat * 333 / 2 ^ 32)
    (t699 : v699.toNat = v401.toNat * 333 % 2 ^ 32) :
    v699.toNat + 2 ^ 32 * v697.toNat = v401.toNat * 333 := by
  have := v401.isLt; have := v697.isLt; have := v699.isLt
  generalize v401.toNat = n401 at *
  generalize v697.toNat = n697 at *
  generalize v699.toNat = n699 at *
  omega

theorem smm_v_PN4L3 {v470 v709 v710 : Word}
    (t709 : v709.toNat = v470.toNat * 502512965 % 2 ^ 32)
    (t710 : v710.toNat = v470.toNat * 502512965 / 2 ^ 32) :
    v709.toNat + 2 ^ 32 * v710.toNat = v470.toNat * 502512965 := by
  have := v470.isLt; have := v709.isLt; have := v710.isLt
  generalize v470.toNat = n470 at *
  generalize v709.toNat = n709 at *
  generalize v710.toNat = n710 at *
  omega

theorem smm_v_PN5L2 {v523 v713 v724 : Word}
    (t713 : v713.toNat = v523.toNat * 501691798 % 2 ^ 32)
    (t724 : v724.toNat = v523.toNat * 501691798 / 2 ^ 32) :
    v713.toNat + 2 ^ 32 * v724.toNat = v523.toNat * 501691798 := by
  have := v523.isLt; have := v713.isLt; have := v724.isLt
  generalize v523.toNat = n523 at *
  generalize v713.toNat = n713 at *
  generalize v724.toNat = n724 at *
  omega

theorem smm_v_PN6L1 {v662 v716 v728 : Word}
    (t716 : v716.toNat = v662.toNat * 9640146 % 2 ^ 32)
    (t728 : v728.toNat = v662.toNat * 9640146 / 2 ^ 32) :
    v716.toNat + 2 ^ 32 * v728.toNat = v662.toNat * 9640146 := by
  have := v662.isLt; have := v716.isLt; have := v728.isLt
  generalize v662.toNat = n662 at *
  generalize v716.toNat = n716 at *
  generalize v728.toNat = n728 at *
  omega

theorem smm_v_S7 {v697 v699 v704 v707 v709 v710 v713 v714 v716 v718 v719 v721 v722 v723 v724 v725 v726 v727 v728 v729 v730 v736 v737 v738 v741 v742 v743 v744 v745 v746 v748 v750 : Word}
    (t714 : v714.toNat = (v707.toNat + v697.toNat) % 2 ^ 32)
    (t719 : v718.toNat + 2 ^ 32 * v719.toNat = v699.toNat + v704.toNat)
    (t722 : v722.toNat = (v714.toNat + v719.toNat) % 2 ^ 32)
    (t725 : v725.toNat = (v710.toNat + v722.toNat) % 2 ^ 32)
    (t729 : v723.toNat + 2 ^ 32 * v729.toNat = v709.toNat + v718.toNat)
    (t736 : v736.toNat = (v729.toNat + v725.toNat) % 2 ^ 32)
    (t737 : v737.toNat = (v736.toNat + v724.toNat) % 2 ^ 32)
    (t738 : v726.toNat + 2 ^ 32 * v738.toNat = v713.toNat + v723.toNat)
    (t741 : v741.toNat = (v737.toNat + v738.toNat) % 2 ^ 32)
    (t742 : v742.toNat = (v741.toNat + v728.toNat) % 2 ^ 32)
    (t743 : v727.toNat + 2 ^ 32 * v743.toNat = v726.toNat + v716.toNat)
    (t744 : v744.toNat = (v743.toNat + v742.toNat) % 2 ^ 32)
    (t746 : v746.toNat = (v744.toNat + v745.toNat) % 2 ^ 32)
    (t748 : v730.toNat + 2 ^ 32 * v748.toNat = v727.toNat + v721.toNat)
    (t750 : v750.toNat = (v746.toNat + v748.toNat) % 2 ^ 32) :
    v730.toNat + 2 ^ 32 * v750.toNat = ((v721.toNat + 2 ^ 32 * v745.toNat) + (v704.toNat + 2 ^ 32 * v707.toNat) + (v699.toNat + 2 ^ 32 * v697.toNat) + (v709.toNat + 2 ^ 32 * v710.toNat) + (v713.toNat + 2 ^ 32 * v724.toNat) + (v716.toNat + 2 ^ 32 * v728.toNat)) % 2 ^ 64 := by
  obtain ⟨q714, eq714⟩ := mod_q t714; clear t714
  obtain ⟨q722, eq722⟩ := mod_q t722; clear t722
  obtain ⟨q725, eq725⟩ := mod_q t725; clear t725
  obtain ⟨q736, eq736⟩ := mod_q t736; clear t736
  obtain ⟨q737, eq737⟩ := mod_q t737; clear t737
  obtain ⟨q741, eq741⟩ := mod_q t741; clear t741
  obtain ⟨q742, eq742⟩ := mod_q t742; clear t742
  obtain ⟨q744, eq744⟩ := mod_q t744; clear t744
  obtain ⟨q746, eq746⟩ := mod_q t746; clear t746
  obtain ⟨q750, eq750⟩ := mod_q t750; clear t750
  have key : v730.toNat + 2 ^ 32 * v750.toNat + 2 ^ 64 * (q714 + q722 + q725 + q736 + q737 + q741 + q742 + q744 + q746 + q750) = ((v721.toNat + 2 ^ 32 * v745.toNat) + (v704.toNat + 2 ^ 32 * v707.toNat) + (v699.toNat + 2 ^ 32 * v697.toNat) + (v709.toNat + 2 ^ 32 * v710.toNat) + (v713.toNat + 2 ^ 32 * v724.toNat) + (v716.toNat + 2 ^ 32 * v728.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v697.toNat = n697 at *
    generalize v699.toNat = n699 at *
    generalize v704.toNat = n704 at *
    generalize v707.toNat = n707 at *
    generalize v709.toNat = n709 at *
    generalize v710.toNat = n710 at *
    generalize v713.toNat = n713 at *
    generalize v714.toNat = n714 at *
    generalize v716.toNat = n716 at *
    generalize v718.toNat = n718 at *
    generalize v719.toNat = n719 at *
    generalize v721.toNat = n721 at *
    generalize v722.toNat = n722 at *
    generalize v723.toNat = n723 at *
    generalize v724.toNat = n724 at *
    generalize v725.toNat = n725 at *
    generalize v726.toNat = n726 at *
    generalize v727.toNat = n727 at *
    generalize v728.toNat = n728 at *
    generalize v729.toNat = n729 at *
    generalize v730.toNat = n730 at *
    generalize v736.toNat = n736 at *
    generalize v737.toNat = n737 at *
    generalize v738.toNat = n738 at *
    generalize v741.toNat = n741 at *
    generalize v742.toNat = n742 at *
    generalize v743.toNat = n743 at *
    generalize v744.toNat = n744 at *
    generalize v745.toNat = n745 at *
    generalize v746.toNat = n746 at *
    generalize v748.toNat = n748 at *
    generalize v750.toNat = n750 at *
    omega
  exact smm_key key (smm_lt v730 v750)

theorem smm_v_N7 {v730 v733 v747 v750 : Word}
    (t733 : v733.toNat = v730.toNat * 307527195 % 2 ^ 32)
    (t747 : v747.toNat = v733.toNat % 2 ^ 29) :
    v747.toNat = ((v730.toNat + 2 ^ 32 * v750.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v730.isLt; have := v733.isLt; have := v747.isLt; have := v750.isLt
  generalize v730.toNat = n730 at *
  generalize v733.toNat = n733 at *
  generalize v747.toNat = n747 at *
  generalize v750.toNat = n750 at *
  omega

theorem smm_v_PN7L0 {v747 v749 v783 : Word}
    (t749 : v749.toNat = v747.toNat * 485872621 / 2 ^ 32)
    (t783 : v783.toNat = v747.toNat * 485872621 % 2 ^ 32) :
    v783.toNat + 2 ^ 32 * v749.toNat = v747.toNat * 485872621 := by
  have := v747.isLt; have := v749.isLt; have := v783.isLt
  generalize v747.toNat = n747 at *
  generalize v749.toNat = n749 at *
  generalize v783.toNat = n783 at *
  omega

theorem smm_v_T7 {v730 v749 v750 v766 v783 v797 v801 v802 : Word}
    (t766 : v766.toNat = (v750.toNat + v749.toNat) % 2 ^ 32)
    (t801 : v797.toNat + 2 ^ 32 * v801.toNat = v730.toNat + v783.toNat)
    (t802 : v802.toNat = (v766.toNat + v801.toNat) % 2 ^ 32) :
    v797.toNat + 2 ^ 32 * v802.toNat = ((v730.toNat + 2 ^ 32 * v750.toNat) + (v783.toNat + 2 ^ 32 * v749.toNat)) % 2 ^ 64 := by
  obtain ⟨q766, eq766⟩ := mod_q t766; clear t766
  obtain ⟨q802, eq802⟩ := mod_q t802; clear t802
  have key : v797.toNat + 2 ^ 32 * v802.toNat + 2 ^ 64 * (q766 + q802) = ((v730.toNat + 2 ^ 32 * v750.toNat) + (v783.toNat + 2 ^ 32 * v749.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v730.toNat = n730 at *
    generalize v749.toNat = n749 at *
    generalize v750.toNat = n750 at *
    generalize v766.toNat = n766 at *
    generalize v783.toNat = n783 at *
    generalize v797.toNat = n797 at *
    generalize v801.toNat = n801 at *
    generalize v802.toNat = n802 at *
    omega
  exact smm_key key (smm_lt v797 v802)

theorem smm_v_C7 {v797 v802 v804 v813 v814 v838 : Word}
    (t804 : v804.toNat = v797.toNat / 2 ^ 29)
    (t813 : v813.toNat = v802.toNat * 2 ^ 3 % 2 ^ 32)
    (t814 : v814.toNat = v804.toNat + v813.toNat)
    (t838 : v838.toNat = v802.toNat / 2 ^ 29) :
    v814.toNat + 2 ^ 32 * v838.toNat = (v797.toNat + 2 ^ 32 * v802.toNat) / 2 ^ 29 := by
  have := v797.isLt; have := v802.isLt; have := v804.isLt; have := v813.isLt; have := v814.isLt; have := v838.isLt
  generalize v797.toNat = n797 at *
  generalize v802.toNat = n802 at *
  generalize v804.toNat = n804 at *
  generalize v813.toNat = n813 at *
  generalize v814.toNat = n814 at *
  generalize v838.toNat = n838 at *
  omega

theorem smm_v_PN0L8 {v193 v214 v229 v232 v752 v756 : Word}
    (t214 : v214.toNat = v193.toNat * 307527195 % 2 ^ 32)
    (t752 : v752.toNat = v229.toNat / 2 ^ 12)
    (t756 : v756.toNat = v214.toNat * 2 ^ 20 % 2 ^ 32)
    (wN0 : v229.toNat = ((v193.toNat + 2 ^ 32 * v232.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v756.toNat + 2 ^ 32 * v752.toNat = v229.toNat * 1048576 := by
  have := v193.isLt; have := v214.isLt; have := v229.isLt; have := v232.isLt; have := v752.isLt; have := v756.isLt
  generalize v193.toNat = n193 at *
  generalize v214.toNat = n214 at *
  generalize v229.toNat = n229 at *
  generalize v232.toNat = n232 at *
  generalize v752.toNat = n752 at *
  generalize v756.toNat = n756 at *
  omega

theorem smm_v_PN4L4 {v470 v788 v796 : Word}
    (t788 : v788.toNat = v470.toNat * 333 / 2 ^ 32)
    (t796 : v796.toNat = v470.toNat * 333 % 2 ^ 32) :
    v796.toNat + 2 ^ 32 * v788.toNat = v470.toNat * 333 := by
  have := v470.isLt; have := v788.isLt; have := v796.isLt
  generalize v470.toNat = n470 at *
  generalize v788.toNat = n788 at *
  generalize v796.toNat = n796 at *
  omega

theorem smm_v_PN5L3 {v523 v805 v807 : Word}
    (t805 : v805.toNat = v523.toNat * 502512965 % 2 ^ 32)
    (t807 : v807.toNat = v523.toNat * 502512965 / 2 ^ 32) :
    v805.toNat + 2 ^ 32 * v807.toNat = v523.toNat * 502512965 := by
  have := v523.isLt; have := v805.isLt; have := v807.isLt
  generalize v523.toNat = n523 at *
  generalize v805.toNat = n805 at *
  generalize v807.toNat = n807 at *
  omega

theorem smm_v_PN6L2 {v662 v809 v810 : Word}
    (t809 : v809.toNat = v662.toNat * 501691798 % 2 ^ 32)
    (t810 : v810.toNat = v662.toNat * 501691798 / 2 ^ 32) :
    v809.toNat + 2 ^ 32 * v810.toNat = v662.toNat * 501691798 := by
  have := v662.isLt; have := v809.isLt; have := v810.isLt
  generalize v662.toNat = n662 at *
  generalize v809.toNat = n809 at *
  generalize v810.toNat = n810 at *
  omega

theorem smm_v_PN7L1 {v747 v811 v817 : Word}
    (t811 : v811.toNat = v747.toNat * 9640146 % 2 ^ 32)
    (t817 : v817.toNat = v747.toNat * 9640146 / 2 ^ 32) :
    v811.toNat + 2 ^ 32 * v817.toNat = v747.toNat * 9640146 := by
  have := v747.isLt; have := v811.isLt; have := v817.isLt
  generalize v747.toNat = n747 at *
  generalize v811.toNat = n811 at *
  generalize v817.toNat = n817 at *
  omega

theorem smm_v_S8 {v55 v90 v272 v278 v559 v561 v573 v575 v585 v587 v597 v599 v628 v630 v752 v754 v756 v758 v759 v761 v763 v764 v765 v767 v769 v771 v772 v774 v776 v777 v778 v780 v782 v784 v785 v787 v788 v790 v791 v792 v794 v795 v796 v799 v800 v803 v805 v806 v807 v808 v809 v810 v811 v812 v814 v815 v816 v817 v818 v819 v820 v821 v822 v823 v824 v825 v826 v828 v829 v831 v838 v840 v842 v847 : Word}
    (t754 : v754.toNat = (v752.toNat + 2 ^ 32 - v90.toNat) % 2 ^ 32)
    (t758 : v759.toNat + v55.toNat = v756.toNat + 2 ^ 32 * v758.toNat)
    (t761 : v761.toNat = (v758.toNat + 2 ^ 32 - v630.toNat) % 2 ^ 32)
    (t764 : v764.toNat = (v754.toNat + 2 ^ 32 - v761.toNat) % 2 ^ 32)
    (t765 : v763.toNat + 2 ^ 32 * v765.toNat = v628.toNat + v759.toNat)
    (t767 : v767.toNat = (v764.toNat + v765.toNat) % 2 ^ 32)
    (t769 : v769.toNat = (v767.toNat + v587.toNat) % 2 ^ 32)
    (t772 : v771.toNat + 2 ^ 32 * v772.toNat = v585.toNat + v763.toNat)
    (t776 : v776.toNat = (v772.toNat + v597.toNat) % 2 ^ 32)
    (t777 : v774.toNat + 2 ^ 32 * v777.toNat = v599.toNat + v771.toNat)
    (t778 : v778.toNat = (v769.toNat + v776.toNat) % 2 ^ 32)
    (t780 : v780.toNat = (v777.toNat + v561.toNat) % 2 ^ 32)
    (t784 : v784.toNat = (v778.toNat + v780.toNat) % 2 ^ 32)
    (t785 : v782.toNat + 2 ^ 32 * v785.toNat = v559.toNat + v774.toNat)
    (t790 : v790.toNat = (v575.toNat + v785.toNat) % 2 ^ 32)
    (t791 : v787.toNat + 2 ^ 32 * v791.toNat = v573.toNat + v782.toNat)
    (t792 : v792.toNat = (v784.toNat + v790.toNat) % 2 ^ 32)
    (t794 : v794.toNat = (v791.toNat + 2 ^ 32 - v278.toNat) % 2 ^ 32)
    (t795 : v795.toNat = (v792.toNat + v794.toNat) % 2 ^ 32)
    (t799 : v806.toNat + v272.toNat = v787.toNat + 2 ^ 32 * v799.toNat)
    (t800 : v800.toNat = (v795.toNat + 2 ^ 32 - v799.toNat) % 2 ^ 32)
    (t803 : v803.toNat = (v800.toNat + v788.toNat) % 2 ^ 32)
    (t812 : v808.toNat + 2 ^ 32 * v812.toNat = v796.toNat + v806.toNat)
    (t815 : v815.toNat = (v803.toNat + v812.toNat) % 2 ^ 32)
    (t818 : v818.toNat = (v815.toNat + v807.toNat) % 2 ^ 32)
    (t819 : v816.toNat + 2 ^ 32 * v819.toNat = v805.toNat + v808.toNat)
    (t820 : v820.toNat = (v818.toNat + v819.toNat) % 2 ^ 32)
    (t822 : v822.toNat = (v810.toNat + v820.toNat) % 2 ^ 32)
    (t824 : v821.toNat + 2 ^ 32 * v824.toNat = v809.toNat + v816.toNat)
    (t826 : v826.toNat = (v824.toNat + v822.toNat) % 2 ^ 32)
    (t828 : v828.toNat = (v826.toNat + v817.toNat) % 2 ^ 32)
    (t829 : v823.toNat + 2 ^ 32 * v829.toNat = v811.toNat + v821.toNat)
    (t831 : v831.toNat = (v829.toNat + v828.toNat) % 2 ^ 32)
    (t840 : v840.toNat = (v831.toNat + v838.toNat) % 2 ^ 32)
    (t842 : v825.toNat + 2 ^ 32 * v842.toNat = v823.toNat + v814.toNat)
    (t847 : v847.toNat = (v840.toNat + v842.toNat) % 2 ^ 32) :
    v825.toNat + 2 ^ 32 * v847.toNat = ((v814.toNat + 2 ^ 32 * v838.toNat) + (((((v559.toNat + 2 ^ 32 * v561.toNat) + (v585.toNat + 2 ^ 32 * v587.toNat) + (v599.toNat + 2 ^ 32 * v597.toNat) + (v573.toNat + 2 ^ 32 * v575.toNat)) % 2 ^ 64) + (((((v628.toNat + 2 ^ 32 * v630.toNat) + (2 ^ 64 - (v55.toNat + 2 ^ 32 * v90.toNat))) % 2 ^ 64) + (2 ^ 64 - (v272.toNat + 2 ^ 32 * v278.toNat))) % 2 ^ 64)) % 2 ^ 64) + (v756.toNat + 2 ^ 32 * v752.toNat) + (v796.toNat + 2 ^ 32 * v788.toNat) + (v805.toNat + 2 ^ 32 * v807.toNat) + (v809.toNat + 2 ^ 32 * v810.toNat) + (v811.toNat + 2 ^ 32 * v817.toNat)) % 2 ^ 64 := by
  obtain ⟨q754, eq754⟩ := mod_q t754; clear t754
  obtain ⟨q761, eq761⟩ := mod_q t761; clear t761
  obtain ⟨q764, eq764⟩ := mod_q t764; clear t764
  obtain ⟨q767, eq767⟩ := mod_q t767; clear t767
  obtain ⟨q769, eq769⟩ := mod_q t769; clear t769
  obtain ⟨q776, eq776⟩ := mod_q t776; clear t776
  obtain ⟨q778, eq778⟩ := mod_q t778; clear t778
  obtain ⟨q780, eq780⟩ := mod_q t780; clear t780
  obtain ⟨q784, eq784⟩ := mod_q t784; clear t784
  obtain ⟨q790, eq790⟩ := mod_q t790; clear t790
  obtain ⟨q792, eq792⟩ := mod_q t792; clear t792
  obtain ⟨q794, eq794⟩ := mod_q t794; clear t794
  obtain ⟨q795, eq795⟩ := mod_q t795; clear t795
  obtain ⟨q800, eq800⟩ := mod_q t800; clear t800
  obtain ⟨q803, eq803⟩ := mod_q t803; clear t803
  obtain ⟨q815, eq815⟩ := mod_q t815; clear t815
  obtain ⟨q818, eq818⟩ := mod_q t818; clear t818
  obtain ⟨q820, eq820⟩ := mod_q t820; clear t820
  obtain ⟨q822, eq822⟩ := mod_q t822; clear t822
  obtain ⟨q826, eq826⟩ := mod_q t826; clear t826
  obtain ⟨q828, eq828⟩ := mod_q t828; clear t828
  obtain ⟨q831, eq831⟩ := mod_q t831; clear t831
  obtain ⟨q840, eq840⟩ := mod_q t840; clear t840
  obtain ⟨q847, eq847⟩ := mod_q t847; clear t847
  obtain ⟨k0, ek0⟩ : ∃ k, ((v628.toNat + 2 ^ 32 * v630.toNat) + (2 ^ 64 - (v55.toNat + 2 ^ 32 * v90.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((v628.toNat + 2 ^ 32 * v630.toNat) + (2 ^ 64 - (v55.toNat + 2 ^ 32 * v90.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((((v628.toNat + 2 ^ 32 * v630.toNat) + (2 ^ 64 - (v55.toNat + 2 ^ 32 * v90.toNat))) % 2 ^ 64) + (2 ^ 64 - (v272.toNat + 2 ^ 32 * v278.toNat))) % 2 ^ 64 + 2 ^ 64 * k = ((((v628.toNat + 2 ^ 32 * v630.toNat) + (2 ^ 64 - (v55.toNat + 2 ^ 32 * v90.toNat))) % 2 ^ 64) + (2 ^ 64 - (v272.toNat + 2 ^ 32 * v278.toNat))) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k2, ek2⟩ : ∃ k, ((v559.toNat + 2 ^ 32 * v561.toNat) + (v585.toNat + 2 ^ 32 * v587.toNat) + (v599.toNat + 2 ^ 32 * v597.toNat) + (v573.toNat + 2 ^ 32 * v575.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v559.toNat + 2 ^ 32 * v561.toNat) + (v585.toNat + 2 ^ 32 * v587.toNat) + (v599.toNat + 2 ^ 32 * v597.toNat) + (v573.toNat + 2 ^ 32 * v575.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k3, ek3⟩ : ∃ k, ((((v559.toNat + 2 ^ 32 * v561.toNat) + (v585.toNat + 2 ^ 32 * v587.toNat) + (v599.toNat + 2 ^ 32 * v597.toNat) + (v573.toNat + 2 ^ 32 * v575.toNat)) % 2 ^ 64) + (((((v628.toNat + 2 ^ 32 * v630.toNat) + (2 ^ 64 - (v55.toNat + 2 ^ 32 * v90.toNat))) % 2 ^ 64) + (2 ^ 64 - (v272.toNat + 2 ^ 32 * v278.toNat))) % 2 ^ 64)) % 2 ^ 64 + 2 ^ 64 * k = ((((v559.toNat + 2 ^ 32 * v561.toNat) + (v585.toNat + 2 ^ 32 * v587.toNat) + (v599.toNat + 2 ^ 32 * v597.toNat) + (v573.toNat + 2 ^ 32 * v575.toNat)) % 2 ^ 64) + (((((v628.toNat + 2 ^ 32 * v630.toNat) + (2 ^ 64 - (v55.toNat + 2 ^ 32 * v90.toNat))) % 2 ^ 64) + (2 ^ 64 - (v272.toNat + 2 ^ 32 * v278.toNat))) % 2 ^ 64)) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v825.toNat + 2 ^ 32 * v847.toNat + 2 ^ 64 * (q754 + q764 + q767 + q769 + q776 + q778 + q780 + q784 + q790 + q792 + q794 + q795 + q800 + q803 + q815 + q818 + q820 + q822 + q826 + q828 + q831 + q840 + q847) = ((v814.toNat + 2 ^ 32 * v838.toNat) + (((((v559.toNat + 2 ^ 32 * v561.toNat) + (v585.toNat + 2 ^ 32 * v587.toNat) + (v599.toNat + 2 ^ 32 * v597.toNat) + (v573.toNat + 2 ^ 32 * v575.toNat)) % 2 ^ 64) + (((((v628.toNat + 2 ^ 32 * v630.toNat) + (2 ^ 64 - (v55.toNat + 2 ^ 32 * v90.toNat))) % 2 ^ 64) + (2 ^ 64 - (v272.toNat + 2 ^ 32 * v278.toNat))) % 2 ^ 64)) % 2 ^ 64) + (v756.toNat + 2 ^ 32 * v752.toNat) + (v796.toNat + 2 ^ 32 * v788.toNat) + (v805.toNat + 2 ^ 32 * v807.toNat) + (v809.toNat + 2 ^ 32 * v810.toNat) + (v811.toNat + 2 ^ 32 * v817.toNat)) + 2 ^ 64 * (q761 + k3 + k2 + k1 + k0 + 1) := by
    have := v55.isLt; have := v90.isLt; have := v272.isLt; have := v278.isLt; have := v630.isLt; have := v761.isLt; have := v799.isLt; skip
    generalize v55.toNat = n55 at *
    generalize v90.toNat = n90 at *
    generalize v272.toNat = n272 at *
    generalize v278.toNat = n278 at *
    generalize v559.toNat = n559 at *
    generalize v561.toNat = n561 at *
    generalize v573.toNat = n573 at *
    generalize v575.toNat = n575 at *
    generalize v585.toNat = n585 at *
    generalize v587.toNat = n587 at *
    generalize v597.toNat = n597 at *
    generalize v599.toNat = n599 at *
    generalize v628.toNat = n628 at *
    generalize v630.toNat = n630 at *
    generalize v752.toNat = n752 at *
    generalize v754.toNat = n754 at *
    generalize v756.toNat = n756 at *
    generalize v758.toNat = n758 at *
    generalize v759.toNat = n759 at *
    generalize v761.toNat = n761 at *
    generalize v763.toNat = n763 at *
    generalize v764.toNat = n764 at *
    generalize v765.toNat = n765 at *
    generalize v767.toNat = n767 at *
    generalize v769.toNat = n769 at *
    generalize v771.toNat = n771 at *
    generalize v772.toNat = n772 at *
    generalize v774.toNat = n774 at *
    generalize v776.toNat = n776 at *
    generalize v777.toNat = n777 at *
    generalize v778.toNat = n778 at *
    generalize v780.toNat = n780 at *
    generalize v782.toNat = n782 at *
    generalize v784.toNat = n784 at *
    generalize v785.toNat = n785 at *
    generalize v787.toNat = n787 at *
    generalize v788.toNat = n788 at *
    generalize v790.toNat = n790 at *
    generalize v791.toNat = n791 at *
    generalize v792.toNat = n792 at *
    generalize v794.toNat = n794 at *
    generalize v795.toNat = n795 at *
    generalize v796.toNat = n796 at *
    generalize v799.toNat = n799 at *
    generalize v800.toNat = n800 at *
    generalize v803.toNat = n803 at *
    generalize v805.toNat = n805 at *
    generalize v806.toNat = n806 at *
    generalize v807.toNat = n807 at *
    generalize v808.toNat = n808 at *
    generalize v809.toNat = n809 at *
    generalize v810.toNat = n810 at *
    generalize v811.toNat = n811 at *
    generalize v812.toNat = n812 at *
    generalize v814.toNat = n814 at *
    generalize v815.toNat = n815 at *
    generalize v816.toNat = n816 at *
    generalize v817.toNat = n817 at *
    generalize v818.toNat = n818 at *
    generalize v819.toNat = n819 at *
    generalize v820.toNat = n820 at *
    generalize v821.toNat = n821 at *
    generalize v822.toNat = n822 at *
    generalize v823.toNat = n823 at *
    generalize v824.toNat = n824 at *
    generalize v825.toNat = n825 at *
    generalize v826.toNat = n826 at *
    generalize v828.toNat = n828 at *
    generalize v829.toNat = n829 at *
    generalize v831.toNat = n831 at *
    generalize v838.toNat = n838 at *
    generalize v840.toNat = n840 at *
    generalize v842.toNat = n842 at *
    generalize v847.toNat = n847 at *
    omega
  exact smm_key key (smm_lt v825 v847)

theorem smm_v_N8 {v825 v827 v843 v847 : Word}
    (t827 : v827.toNat = v825.toNat * 307527195 % 2 ^ 32)
    (t843 : v843.toNat = v827.toNat % 2 ^ 29) :
    v843.toNat = ((v825.toNat + 2 ^ 32 * v847.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29 := by
  have := v825.isLt; have := v827.isLt; have := v843.isLt; have := v847.isLt
  generalize v825.toNat = n825 at *
  generalize v827.toNat = n827 at *
  generalize v843.toNat = n843 at *
  generalize v847.toNat = n847 at *
  omega

theorem smm_v_PN8L0 {v843 v844 v858 : Word}
    (t844 : v844.toNat = v843.toNat * 485872621 / 2 ^ 32)
    (t858 : v858.toNat = v843.toNat * 485872621 % 2 ^ 32) :
    v858.toNat + 2 ^ 32 * v844.toNat = v843.toNat * 485872621 := by
  have := v843.isLt; have := v844.isLt; have := v858.isLt
  generalize v843.toNat = n843 at *
  generalize v844.toNat = n844 at *
  generalize v858.toNat = n858 at *
  omega

theorem smm_v_T8 {v825 v844 v847 v858 v860 v876 v880 v885 : Word}
    (t860 : v860.toNat = (v847.toNat + v844.toNat) % 2 ^ 32)
    (t880 : v876.toNat + 2 ^ 32 * v880.toNat = v858.toNat + v825.toNat)
    (t885 : v885.toNat = (v860.toNat + v880.toNat) % 2 ^ 32) :
    v876.toNat + 2 ^ 32 * v885.toNat = ((v825.toNat + 2 ^ 32 * v847.toNat) + (v858.toNat + 2 ^ 32 * v844.toNat)) % 2 ^ 64 := by
  obtain ⟨q860, eq860⟩ := mod_q t860; clear t860
  obtain ⟨q885, eq885⟩ := mod_q t885; clear t885
  have key : v876.toNat + 2 ^ 32 * v885.toNat + 2 ^ 64 * (q860 + q885) = ((v825.toNat + 2 ^ 32 * v847.toNat) + (v858.toNat + 2 ^ 32 * v844.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v825.toNat = n825 at *
    generalize v844.toNat = n844 at *
    generalize v847.toNat = n847 at *
    generalize v858.toNat = n858 at *
    generalize v860.toNat = n860 at *
    generalize v876.toNat = n876 at *
    generalize v880.toNat = n880 at *
    generalize v885.toNat = n885 at *
    omega
  exact smm_key key (smm_lt v876 v885)

theorem smm_v_C8 {v876 v885 v913 v914 v915 v916 : Word}
    (t913 : v913.toNat = v876.toNat / 2 ^ 29)
    (t914 : v914.toNat = v885.toNat * 2 ^ 3 % 2 ^ 32)
    (t915 : v915.toNat = v885.toNat / 2 ^ 29)
    (t916 : v916.toNat = v913.toNat + v914.toNat) :
    v916.toNat + 2 ^ 32 * v915.toNat = (v876.toNat + 2 ^ 32 * v885.toNat) / 2 ^ 29 := by
  have := v876.isLt; have := v885.isLt; have := v913.isLt; have := v914.isLt; have := v915.isLt; have := v916.isLt
  generalize v876.toNat = n876 at *
  generalize v885.toNat = n885 at *
  generalize v913.toNat = n913 at *
  generalize v914.toNat = n914 at *
  generalize v915.toNat = n915 at *
  generalize v916.toNat = n916 at *
  omega

theorem smm_v_PN1L8 {v263 v266 v285 v298 v853 v855 : Word}
    (t266 : v266.toNat = v263.toNat * 307527195 % 2 ^ 32)
    (t853 : v853.toNat = v285.toNat / 2 ^ 12)
    (t855 : v855.toNat = v266.toNat * 2 ^ 20 % 2 ^ 32)
    (wN1 : v285.toNat = ((v263.toNat + 2 ^ 32 * v298.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v855.toNat + 2 ^ 32 * v853.toNat = v285.toNat * 1048576 := by
  have := v263.isLt; have := v266.isLt; have := v285.isLt; have := v298.isLt; have := v853.isLt; have := v855.isLt
  generalize v263.toNat = n263 at *
  generalize v266.toNat = n266 at *
  generalize v285.toNat = n285 at *
  generalize v298.toNat = n298 at *
  generalize v853.toNat = n853 at *
  generalize v855.toNat = n855 at *
  omega

theorem smm_v_PN5L4 {v523 v879 v884 : Word}
    (t879 : v879.toNat = v523.toNat * 333 / 2 ^ 32)
    (t884 : v884.toNat = v523.toNat * 333 % 2 ^ 32) :
    v884.toNat + 2 ^ 32 * v879.toNat = v523.toNat * 333 := by
  have := v523.isLt; have := v879.isLt; have := v884.isLt
  generalize v523.toNat = n523 at *
  generalize v879.toNat = n879 at *
  generalize v884.toNat = n884 at *
  omega

theorem smm_v_PN6L3 {v662 v887 v891 : Word}
    (t887 : v887.toNat = v662.toNat * 502512965 % 2 ^ 32)
    (t891 : v891.toNat = v662.toNat * 502512965 / 2 ^ 32) :
    v887.toNat + 2 ^ 32 * v891.toNat = v662.toNat * 502512965 := by
  have := v662.isLt; have := v887.isLt; have := v891.isLt
  generalize v662.toNat = n662 at *
  generalize v887.toNat = n887 at *
  generalize v891.toNat = n891 at *
  omega

theorem smm_v_PN7L2 {v747 v893 v895 : Word}
    (t893 : v893.toNat = v747.toNat * 501691798 % 2 ^ 32)
    (t895 : v895.toNat = v747.toNat * 501691798 / 2 ^ 32) :
    v893.toNat + 2 ^ 32 * v895.toNat = v747.toNat * 501691798 := by
  have := v747.isLt; have := v893.isLt; have := v895.isLt
  generalize v747.toNat = n747 at *
  generalize v893.toNat = n893 at *
  generalize v895.toNat = n895 at *
  omega

theorem smm_v_PN8L1 {v843 v897 v898 : Word}
    (t897 : v897.toNat = v843.toNat * 9640146 % 2 ^ 32)
    (t898 : v898.toNat = v843.toNat * 9640146 / 2 ^ 32) :
    v897.toNat + 2 ^ 32 * v898.toNat = v843.toNat * 9640146 := by
  have := v843.isLt; have := v897.isLt; have := v898.isLt
  generalize v843.toNat = n843 at *
  generalize v897.toNat = n897 at *
  generalize v898.toNat = n898 at *
  omega

theorem smm_v_S9 {v122 v139 v274 v280 v564 v566 v578 v580 v589 v591 v601 v604 v612 v616 v834 v837 v839 v841 v846 v848 v850 v851 v853 v855 v856 v857 v859 v861 v863 v865 v866 v868 v870 v871 v872 v874 v875 v878 v879 v881 v883 v884 v886 v887 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v915 v916 v917 v946 v947 v950 : Word}
    (t834 : v834.toNat = (v566.toNat + v580.toNat) % 2 ^ 32)
    (t839 : v837.toNat + 2 ^ 32 * v839.toNat = v564.toNat + v578.toNat)
    (t841 : v841.toNat = (v834.toNat + v839.toNat) % 2 ^ 32)
    (t846 : v851.toNat + v122.toNat = v837.toNat + 2 ^ 32 * v846.toNat)
    (t848 : v848.toNat = (v841.toNat + 2 ^ 32 - v846.toNat) % 2 ^ 32)
    (t850 : v850.toNat = (v848.toNat + 2 ^ 32 - v139.toNat) % 2 ^ 32)
    (t856 : v856.toNat = (v850.toNat + v853.toNat) % 2 ^ 32)
    (t859 : v857.toNat + 2 ^ 32 * v859.toNat = v855.toNat + v851.toNat)
    (t861 : v861.toNat = (v856.toNat + v859.toNat) % 2 ^ 32)
    (t863 : v863.toNat = (v861.toNat + v612.toNat) % 2 ^ 32)
    (t866 : v865.toNat + 2 ^ 32 * v866.toNat = v616.toNat + v857.toNat)
    (t870 : v870.toNat = (v866.toNat + v591.toNat) % 2 ^ 32)
    (t871 : v868.toNat + 2 ^ 32 * v871.toNat = v589.toNat + v865.toNat)
    (t872 : v872.toNat = (v863.toNat + v870.toNat) % 2 ^ 32)
    (t874 : v874.toNat = (v871.toNat + v604.toNat) % 2 ^ 32)
    (t875 : v875.toNat = (v872.toNat + v874.toNat) % 2 ^ 32)
    (t881 : v878.toNat + 2 ^ 32 * v881.toNat = v601.toNat + v868.toNat)
    (t883 : v883.toNat = (v881.toNat + 2 ^ 32 - v280.toNat) % 2 ^ 32)
    (t886 : v886.toNat = (v875.toNat + v883.toNat) % 2 ^ 32)
    (t889 : v894.toNat + v274.toNat = v878.toNat + 2 ^ 32 * v889.toNat)
    (t890 : v890.toNat = (v886.toNat + 2 ^ 32 - v889.toNat) % 2 ^ 32)
    (t892 : v892.toNat = (v890.toNat + v879.toNat) % 2 ^ 32)
    (t899 : v896.toNat + 2 ^ 32 * v899.toNat = v884.toNat + v894.toNat)
    (t900 : v900.toNat = (v892.toNat + v899.toNat) % 2 ^ 32)
    (t902 : v902.toNat = (v900.toNat + v891.toNat) % 2 ^ 32)
    (t903 : v901.toNat + 2 ^ 32 * v903.toNat = v887.toNat + v896.toNat)
    (t904 : v904.toNat = (v902.toNat + v903.toNat) % 2 ^ 32)
    (t906 : v906.toNat = (v895.toNat + v904.toNat) % 2 ^ 32)
    (t907 : v905.toNat + 2 ^ 32 * v907.toNat = v893.toNat + v901.toNat)
    (t908 : v908.toNat = (v906.toNat + v907.toNat) % 2 ^ 32)
    (t910 : v910.toNat = (v908.toNat + v898.toNat) % 2 ^ 32)
    (t911 : v909.toNat + 2 ^ 32 * v911.toNat = v897.toNat + v905.toNat)
    (t912 : v912.toNat = (v910.toNat + v911.toNat) % 2 ^ 32)
    (t917 : v917.toNat = (v915.toNat + v912.toNat) % 2 ^ 32)
    (t947 : v946.toNat + 2 ^ 32 * v947.toNat = v909.toNat + v916.toNat)
    (t950 : v950.toNat = (v917.toNat + v947.toNat) % 2 ^ 32) :
    v946.toNat + 2 ^ 32 * v950.toNat = ((v916.toNat + 2 ^ 32 * v915.toNat) + (((((v564.toNat + 2 ^ 32 * v566.toNat) + (v589.toNat + 2 ^ 32 * v591.toNat) + (v616.toNat + 2 ^ 32 * v612.toNat) + (v601.toNat + 2 ^ 32 * v604.toNat) + (v578.toNat + 2 ^ 32 * v580.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v274.toNat + 2 ^ 32 * v280.toNat) + (v122.toNat + 2 ^ 32 * v139.toNat)) % 2 ^ 64))) % 2 ^ 64) + (v855.toNat + 2 ^ 32 * v853.toNat) + (v884.toNat + 2 ^ 32 * v879.toNat) + (v887.toNat + 2 ^ 32 * v891.toNat) + (v893.toNat + 2 ^ 32 * v895.toNat) + (v897.toNat + 2 ^ 32 * v898.toNat)) % 2 ^ 64 := by
  obtain ⟨q834, eq834⟩ := mod_q t834; clear t834
  obtain ⟨q841, eq841⟩ := mod_q t841; clear t841
  obtain ⟨q848, eq848⟩ := mod_q t848; clear t848
  obtain ⟨q850, eq850⟩ := mod_q t850; clear t850
  obtain ⟨q856, eq856⟩ := mod_q t856; clear t856
  obtain ⟨q861, eq861⟩ := mod_q t861; clear t861
  obtain ⟨q863, eq863⟩ := mod_q t863; clear t863
  obtain ⟨q870, eq870⟩ := mod_q t870; clear t870
  obtain ⟨q872, eq872⟩ := mod_q t872; clear t872
  obtain ⟨q874, eq874⟩ := mod_q t874; clear t874
  obtain ⟨q875, eq875⟩ := mod_q t875; clear t875
  obtain ⟨q883, eq883⟩ := mod_q t883; clear t883
  obtain ⟨q886, eq886⟩ := mod_q t886; clear t886
  obtain ⟨q890, eq890⟩ := mod_q t890; clear t890
  obtain ⟨q892, eq892⟩ := mod_q t892; clear t892
  obtain ⟨q900, eq900⟩ := mod_q t900; clear t900
  obtain ⟨q902, eq902⟩ := mod_q t902; clear t902
  obtain ⟨q904, eq904⟩ := mod_q t904; clear t904
  obtain ⟨q906, eq906⟩ := mod_q t906; clear t906
  obtain ⟨q908, eq908⟩ := mod_q t908; clear t908
  obtain ⟨q910, eq910⟩ := mod_q t910; clear t910
  obtain ⟨q912, eq912⟩ := mod_q t912; clear t912
  obtain ⟨q917, eq917⟩ := mod_q t917; clear t917
  obtain ⟨q950, eq950⟩ := mod_q t950; clear t950
  obtain ⟨k0, ek0⟩ : ∃ k, ((v274.toNat + 2 ^ 32 * v280.toNat) + (v122.toNat + 2 ^ 32 * v139.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v274.toNat + 2 ^ 32 * v280.toNat) + (v122.toNat + 2 ^ 32 * v139.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k1, ek1⟩ : ∃ k, ((v564.toNat + 2 ^ 32 * v566.toNat) + (v589.toNat + 2 ^ 32 * v591.toNat) + (v616.toNat + 2 ^ 32 * v612.toNat) + (v601.toNat + 2 ^ 32 * v604.toNat) + (v578.toNat + 2 ^ 32 * v580.toNat)) % 2 ^ 64 + 2 ^ 64 * k = ((v564.toNat + 2 ^ 32 * v566.toNat) + (v589.toNat + 2 ^ 32 * v591.toNat) + (v616.toNat + 2 ^ 32 * v612.toNat) + (v601.toNat + 2 ^ 32 * v604.toNat) + (v578.toNat + 2 ^ 32 * v580.toNat)) := ⟨_, Nat.mod_add_div _ _⟩
  obtain ⟨k2, ek2⟩ : ∃ k, ((((v564.toNat + 2 ^ 32 * v566.toNat) + (v589.toNat + 2 ^ 32 * v591.toNat) + (v616.toNat + 2 ^ 32 * v612.toNat) + (v601.toNat + 2 ^ 32 * v604.toNat) + (v578.toNat + 2 ^ 32 * v580.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v274.toNat + 2 ^ 32 * v280.toNat) + (v122.toNat + 2 ^ 32 * v139.toNat)) % 2 ^ 64))) % 2 ^ 64 + 2 ^ 64 * k = ((((v564.toNat + 2 ^ 32 * v566.toNat) + (v589.toNat + 2 ^ 32 * v591.toNat) + (v616.toNat + 2 ^ 32 * v612.toNat) + (v601.toNat + 2 ^ 32 * v604.toNat) + (v578.toNat + 2 ^ 32 * v580.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v274.toNat + 2 ^ 32 * v280.toNat) + (v122.toNat + 2 ^ 32 * v139.toNat)) % 2 ^ 64))) := ⟨_, Nat.mod_add_div _ _⟩
  have key : v946.toNat + 2 ^ 32 * v950.toNat + 2 ^ 64 * (q834 + q841 + q848 + q850 + q856 + q861 + q863 + q870 + q872 + q874 + q875 + q883 + q886 + q890 + q892 + q900 + q902 + q904 + q906 + q908 + q910 + q912 + q917 + q950 + k0) = ((v916.toNat + 2 ^ 32 * v915.toNat) + (((((v564.toNat + 2 ^ 32 * v566.toNat) + (v589.toNat + 2 ^ 32 * v591.toNat) + (v616.toNat + 2 ^ 32 * v612.toNat) + (v601.toNat + 2 ^ 32 * v604.toNat) + (v578.toNat + 2 ^ 32 * v580.toNat)) % 2 ^ 64) + (2 ^ 64 - (((v274.toNat + 2 ^ 32 * v280.toNat) + (v122.toNat + 2 ^ 32 * v139.toNat)) % 2 ^ 64))) % 2 ^ 64) + (v855.toNat + 2 ^ 32 * v853.toNat) + (v884.toNat + 2 ^ 32 * v879.toNat) + (v887.toNat + 2 ^ 32 * v891.toNat) + (v893.toNat + 2 ^ 32 * v895.toNat) + (v897.toNat + 2 ^ 32 * v898.toNat)) + 2 ^ 64 * (k2 + k1 + 3) := by
    have := v122.isLt; have := v139.isLt; have := v274.isLt; have := v280.isLt; have := v846.isLt; have := v889.isLt; skip
    generalize v122.toNat = n122 at *
    generalize v139.toNat = n139 at *
    generalize v274.toNat = n274 at *
    generalize v280.toNat = n280 at *
    generalize v564.toNat = n564 at *
    generalize v566.toNat = n566 at *
    generalize v578.toNat = n578 at *
    generalize v580.toNat = n580 at *
    generalize v589.toNat = n589 at *
    generalize v591.toNat = n591 at *
    generalize v601.toNat = n601 at *
    generalize v604.toNat = n604 at *
    generalize v612.toNat = n612 at *
    generalize v616.toNat = n616 at *
    generalize v834.toNat = n834 at *
    generalize v837.toNat = n837 at *
    generalize v839.toNat = n839 at *
    generalize v841.toNat = n841 at *
    generalize v846.toNat = n846 at *
    generalize v848.toNat = n848 at *
    generalize v850.toNat = n850 at *
    generalize v851.toNat = n851 at *
    generalize v853.toNat = n853 at *
    generalize v855.toNat = n855 at *
    generalize v856.toNat = n856 at *
    generalize v857.toNat = n857 at *
    generalize v859.toNat = n859 at *
    generalize v861.toNat = n861 at *
    generalize v863.toNat = n863 at *
    generalize v865.toNat = n865 at *
    generalize v866.toNat = n866 at *
    generalize v868.toNat = n868 at *
    generalize v870.toNat = n870 at *
    generalize v871.toNat = n871 at *
    generalize v872.toNat = n872 at *
    generalize v874.toNat = n874 at *
    generalize v875.toNat = n875 at *
    generalize v878.toNat = n878 at *
    generalize v879.toNat = n879 at *
    generalize v881.toNat = n881 at *
    generalize v883.toNat = n883 at *
    generalize v884.toNat = n884 at *
    generalize v886.toNat = n886 at *
    generalize v887.toNat = n887 at *
    generalize v889.toNat = n889 at *
    generalize v890.toNat = n890 at *
    generalize v891.toNat = n891 at *
    generalize v892.toNat = n892 at *
    generalize v893.toNat = n893 at *
    generalize v894.toNat = n894 at *
    generalize v895.toNat = n895 at *
    generalize v896.toNat = n896 at *
    generalize v897.toNat = n897 at *
    generalize v898.toNat = n898 at *
    generalize v899.toNat = n899 at *
    generalize v900.toNat = n900 at *
    generalize v901.toNat = n901 at *
    generalize v902.toNat = n902 at *
    generalize v903.toNat = n903 at *
    generalize v904.toNat = n904 at *
    generalize v905.toNat = n905 at *
    generalize v906.toNat = n906 at *
    generalize v907.toNat = n907 at *
    generalize v908.toNat = n908 at *
    generalize v909.toNat = n909 at *
    generalize v910.toNat = n910 at *
    generalize v911.toNat = n911 at *
    generalize v912.toNat = n912 at *
    generalize v915.toNat = n915 at *
    generalize v916.toNat = n916 at *
    generalize v917.toNat = n917 at *
    generalize v946.toNat = n946 at *
    generalize v947.toNat = n947 at *
    generalize v950.toNat = n950 at *
    omega
  exact smm_key key (smm_lt v946 v950)

theorem smm_v_R0 {v946 v950 v1123 : Word}
    (t1123 : v1123.toNat = v946.toNat % 2 ^ 29) :
    v1123.toNat = (v946.toNat + 2 ^ 32 * v950.toNat) % 2 ^ 29 := by
  have := v946.isLt; have := v950.isLt; have := v1123.isLt
  generalize v946.toNat = n946 at *
  generalize v950.toNat = n950 at *
  generalize v1123.toNat = n1123 at *
  omega

theorem smm_v_C9 {v946 v950 v978 v979 v980 v988 : Word}
    (t978 : v978.toNat = v950.toNat * 2 ^ 3 % 2 ^ 32)
    (t979 : v979.toNat = v946.toNat / 2 ^ 29)
    (t980 : v980.toNat = v979.toNat + v978.toNat)
    (t988 : v988.toNat = v950.toNat / 2 ^ 29) :
    v980.toNat + 2 ^ 32 * v988.toNat = (v946.toNat + 2 ^ 32 * v950.toNat) / 2 ^ 29 := by
  have := v946.isLt; have := v950.isLt; have := v978.isLt; have := v979.isLt; have := v980.isLt; have := v988.isLt
  generalize v946.toNat = n946 at *
  generalize v950.toNat = n950 at *
  generalize v978.toNat = n978 at *
  generalize v979.toNat = n979 at *
  generalize v980.toNat = n980 at *
  generalize v988.toNat = n988 at *
  omega

theorem smm_v_PN2L8 {v312 v316 v341 v354 v953 v958 : Word}
    (t316 : v316.toNat = v312.toNat * 307527195 % 2 ^ 32)
    (t953 : v953.toNat = v341.toNat / 2 ^ 12)
    (t958 : v958.toNat = v316.toNat * 2 ^ 20 % 2 ^ 32)
    (wN2 : v341.toNat = ((v312.toNat + 2 ^ 32 * v354.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v958.toNat + 2 ^ 32 * v953.toNat = v341.toNat * 1048576 := by
  have := v312.isLt; have := v316.isLt; have := v341.isLt; have := v354.isLt; have := v953.isLt; have := v958.isLt
  generalize v312.toNat = n312 at *
  generalize v316.toNat = n316 at *
  generalize v341.toNat = n341 at *
  generalize v354.toNat = n354 at *
  generalize v953.toNat = n953 at *
  generalize v958.toNat = n958 at *
  omega

theorem smm_v_PN6L4 {v662 v954 v956 : Word}
    (t954 : v954.toNat = v662.toNat * 333 % 2 ^ 32)
    (t956 : v956.toNat = v662.toNat * 333 / 2 ^ 32) :
    v954.toNat + 2 ^ 32 * v956.toNat = v662.toNat * 333 := by
  have := v662.isLt; have := v954.isLt; have := v956.isLt
  generalize v662.toNat = n662 at *
  generalize v954.toNat = n954 at *
  generalize v956.toNat = n956 at *
  omega

theorem smm_v_PN7L3 {v747 v959 v961 : Word}
    (t959 : v959.toNat = v747.toNat * 502512965 % 2 ^ 32)
    (t961 : v961.toNat = v747.toNat * 502512965 / 2 ^ 32) :
    v959.toNat + 2 ^ 32 * v961.toNat = v747.toNat * 502512965 := by
  have := v747.isLt; have := v959.isLt; have := v961.isLt
  generalize v747.toNat = n747 at *
  generalize v959.toNat = n959 at *
  generalize v961.toNat = n961 at *
  omega

theorem smm_v_PN8L2 {v843 v963 v964 : Word}
    (t963 : v963.toNat = v843.toNat * 501691798 % 2 ^ 32)
    (t964 : v964.toNat = v843.toNat * 501691798 / 2 ^ 32) :
    v963.toNat + 2 ^ 32 * v964.toNat = v843.toNat * 501691798 := by
  have := v843.isLt; have := v963.isLt; have := v964.isLt
  generalize v843.toNat = n843 at *
  generalize v963.toNat = n963 at *
  generalize v964.toNat = n964 at *
  omega

theorem smm_v_S10 {v951 v953 v954 v955 v956 v958 v959 v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v973 v974 v975 v976 v977 v980 v981 v988 v990 v992 v996 v998 : Word}
    (t955 : v955.toNat = (v951.toNat + v953.toNat) % 2 ^ 32)
    (t965 : v962.toNat + 2 ^ 32 * v965.toNat = v958.toNat + v960.toNat)
    (t966 : v966.toNat = (v955.toNat + v965.toNat) % 2 ^ 32)
    (t968 : v968.toNat = (v966.toNat + v956.toNat) % 2 ^ 32)
    (t969 : v967.toNat + 2 ^ 32 * v969.toNat = v954.toNat + v962.toNat)
    (t970 : v970.toNat = (v968.toNat + v969.toNat) % 2 ^ 32)
    (t972 : v972.toNat = (v970.toNat + v961.toNat) % 2 ^ 32)
    (t973 : v971.toNat + 2 ^ 32 * v973.toNat = v959.toNat + v967.toNat)
    (t974 : v974.toNat = (v972.toNat + v973.toNat) % 2 ^ 32)
    (t976 : v976.toNat = (v974.toNat + v964.toNat) % 2 ^ 32)
    (t977 : v975.toNat + 2 ^ 32 * v977.toNat = v963.toNat + v971.toNat)
    (t981 : v981.toNat = (v976.toNat + v977.toNat) % 2 ^ 32)
    (t990 : v990.toNat = (v988.toNat + v981.toNat) % 2 ^ 32)
    (t996 : v992.toNat + 2 ^ 32 * v996.toNat = v975.toNat + v980.toNat)
    (t998 : v998.toNat = (v990.toNat + v996.toNat) % 2 ^ 32) :
    v992.toNat + 2 ^ 32 * v998.toNat = ((v980.toNat + 2 ^ 32 * v988.toNat) + (v960.toNat + 2 ^ 32 * v951.toNat) + (v958.toNat + 2 ^ 32 * v953.toNat) + (v954.toNat + 2 ^ 32 * v956.toNat) + (v959.toNat + 2 ^ 32 * v961.toNat) + (v963.toNat + 2 ^ 32 * v964.toNat)) % 2 ^ 64 := by
  obtain ⟨q955, eq955⟩ := mod_q t955; clear t955
  obtain ⟨q966, eq966⟩ := mod_q t966; clear t966
  obtain ⟨q968, eq968⟩ := mod_q t968; clear t968
  obtain ⟨q970, eq970⟩ := mod_q t970; clear t970
  obtain ⟨q972, eq972⟩ := mod_q t972; clear t972
  obtain ⟨q974, eq974⟩ := mod_q t974; clear t974
  obtain ⟨q976, eq976⟩ := mod_q t976; clear t976
  obtain ⟨q981, eq981⟩ := mod_q t981; clear t981
  obtain ⟨q990, eq990⟩ := mod_q t990; clear t990
  obtain ⟨q998, eq998⟩ := mod_q t998; clear t998
  have key : v992.toNat + 2 ^ 32 * v998.toNat + 2 ^ 64 * (q955 + q966 + q968 + q970 + q972 + q974 + q976 + q981 + q990 + q998) = ((v980.toNat + 2 ^ 32 * v988.toNat) + (v960.toNat + 2 ^ 32 * v951.toNat) + (v958.toNat + 2 ^ 32 * v953.toNat) + (v954.toNat + 2 ^ 32 * v956.toNat) + (v959.toNat + 2 ^ 32 * v961.toNat) + (v963.toNat + 2 ^ 32 * v964.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v951.toNat = n951 at *
    generalize v953.toNat = n953 at *
    generalize v954.toNat = n954 at *
    generalize v955.toNat = n955 at *
    generalize v956.toNat = n956 at *
    generalize v958.toNat = n958 at *
    generalize v959.toNat = n959 at *
    generalize v960.toNat = n960 at *
    generalize v961.toNat = n961 at *
    generalize v962.toNat = n962 at *
    generalize v963.toNat = n963 at *
    generalize v964.toNat = n964 at *
    generalize v965.toNat = n965 at *
    generalize v966.toNat = n966 at *
    generalize v967.toNat = n967 at *
    generalize v968.toNat = n968 at *
    generalize v969.toNat = n969 at *
    generalize v970.toNat = n970 at *
    generalize v971.toNat = n971 at *
    generalize v972.toNat = n972 at *
    generalize v973.toNat = n973 at *
    generalize v974.toNat = n974 at *
    generalize v975.toNat = n975 at *
    generalize v976.toNat = n976 at *
    generalize v977.toNat = n977 at *
    generalize v980.toNat = n980 at *
    generalize v981.toNat = n981 at *
    generalize v988.toNat = n988 at *
    generalize v990.toNat = n990 at *
    generalize v992.toNat = n992 at *
    generalize v996.toNat = n996 at *
    generalize v998.toNat = n998 at *
    omega
  exact smm_key key (smm_lt v992 v998)

theorem smm_v_R1 {v992 v998 v1124 : Word}
    (t1124 : v1124.toNat = v992.toNat % 2 ^ 29) :
    v1124.toNat = (v992.toNat + 2 ^ 32 * v998.toNat) % 2 ^ 29 := by
  have := v992.isLt; have := v998.isLt; have := v1124.isLt
  generalize v992.toNat = n992 at *
  generalize v998.toNat = n998 at *
  generalize v1124.toNat = n1124 at *
  omega

theorem smm_v_C10 {v992 v998 v1032 v1033 v1034 v1036 : Word}
    (t1032 : v1032.toNat = v998.toNat * 2 ^ 3 % 2 ^ 32)
    (t1033 : v1033.toNat = v992.toNat / 2 ^ 29)
    (t1034 : v1034.toNat = v1033.toNat + v1032.toNat)
    (t1036 : v1036.toNat = v998.toNat / 2 ^ 29) :
    v1034.toNat + 2 ^ 32 * v1036.toNat = (v992.toNat + 2 ^ 32 * v998.toNat) / 2 ^ 29 := by
  have := v992.isLt; have := v998.isLt; have := v1032.isLt; have := v1033.isLt; have := v1034.isLt; have := v1036.isLt
  generalize v992.toNat = n992 at *
  generalize v998.toNat = n998 at *
  generalize v1032.toNat = n1032 at *
  generalize v1033.toNat = n1033 at *
  generalize v1034.toNat = n1034 at *
  generalize v1036.toNat = n1036 at *
  omega

theorem smm_v_PN3L8 {v379 v382 v401 v415 v1017 v1020 : Word}
    (t382 : v382.toNat = v379.toNat * 307527195 % 2 ^ 32)
    (t1017 : v1017.toNat = v382.toNat * 2 ^ 20 % 2 ^ 32)
    (t1020 : v1020.toNat = v401.toNat / 2 ^ 12)
    (wN3 : v401.toNat = ((v379.toNat + 2 ^ 32 * v415.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1017.toNat + 2 ^ 32 * v1020.toNat = v401.toNat * 1048576 := by
  have := v379.isLt; have := v382.isLt; have := v401.isLt; have := v415.isLt; have := v1017.isLt; have := v1020.isLt
  generalize v379.toNat = n379 at *
  generalize v382.toNat = n382 at *
  generalize v401.toNat = n401 at *
  generalize v415.toNat = n415 at *
  generalize v1017.toNat = n1017 at *
  generalize v1020.toNat = n1020 at *
  omega

theorem smm_v_PN7L4 {v747 v1011 v1013 : Word}
    (t1011 : v1011.toNat = v747.toNat * 333 % 2 ^ 32)
    (t1013 : v1013.toNat = v747.toNat * 333 / 2 ^ 32) :
    v1011.toNat + 2 ^ 32 * v1013.toNat = v747.toNat * 333 := by
  have := v747.isLt; have := v1011.isLt; have := v1013.isLt
  generalize v747.toNat = n747 at *
  generalize v1011.toNat = n1011 at *
  generalize v1013.toNat = n1013 at *
  omega

theorem smm_v_PN8L3 {v843 v1015 v1018 : Word}
    (t1015 : v1015.toNat = v843.toNat * 502512965 % 2 ^ 32)
    (t1018 : v1018.toNat = v843.toNat * 502512965 / 2 ^ 32) :
    v1015.toNat + 2 ^ 32 * v1018.toNat = v843.toNat * 502512965 := by
  have := v843.isLt; have := v1015.isLt; have := v1018.isLt
  generalize v843.toNat = n843 at *
  generalize v1015.toNat = n1015 at *
  generalize v1018.toNat = n1018 at *
  omega

theorem smm_v_S11 {v1010 v1011 v1013 v1014 v1015 v1017 v1018 v1020 v1021 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1029 v1030 v1031 v1034 v1035 v1036 v1037 v1040 v1041 v1042 : Word}
    (t1022 : v1022.toNat = (v1020.toNat + v1014.toNat) % 2 ^ 32)
    (t1023 : v1021.toNat + 2 ^ 32 * v1023.toNat = v1017.toNat + v1010.toNat)
    (t1024 : v1024.toNat = (v1022.toNat + v1023.toNat) % 2 ^ 32)
    (t1026 : v1026.toNat = (v1024.toNat + v1013.toNat) % 2 ^ 32)
    (t1027 : v1025.toNat + 2 ^ 32 * v1027.toNat = v1011.toNat + v1021.toNat)
    (t1028 : v1028.toNat = (v1026.toNat + v1027.toNat) % 2 ^ 32)
    (t1030 : v1030.toNat = (v1028.toNat + v1018.toNat) % 2 ^ 32)
    (t1031 : v1029.toNat + 2 ^ 32 * v1031.toNat = v1015.toNat + v1025.toNat)
    (t1035 : v1035.toNat = (v1030.toNat + v1031.toNat) % 2 ^ 32)
    (t1040 : v1040.toNat = (v1035.toNat + v1036.toNat) % 2 ^ 32)
    (t1041 : v1037.toNat + 2 ^ 32 * v1041.toNat = v1029.toNat + v1034.toNat)
    (t1042 : v1042.toNat = (v1040.toNat + v1041.toNat) % 2 ^ 32) :
    v1037.toNat + 2 ^ 32 * v1042.toNat = ((v1034.toNat + 2 ^ 32 * v1036.toNat) + (v1010.toNat + 2 ^ 32 * v1014.toNat) + (v1017.toNat + 2 ^ 32 * v1020.toNat) + (v1011.toNat + 2 ^ 32 * v1013.toNat) + (v1015.toNat + 2 ^ 32 * v1018.toNat)) % 2 ^ 64 := by
  obtain ⟨q1022, eq1022⟩ := mod_q t1022; clear t1022
  obtain ⟨q1024, eq1024⟩ := mod_q t1024; clear t1024
  obtain ⟨q1026, eq1026⟩ := mod_q t1026; clear t1026
  obtain ⟨q1028, eq1028⟩ := mod_q t1028; clear t1028
  obtain ⟨q1030, eq1030⟩ := mod_q t1030; clear t1030
  obtain ⟨q1035, eq1035⟩ := mod_q t1035; clear t1035
  obtain ⟨q1040, eq1040⟩ := mod_q t1040; clear t1040
  obtain ⟨q1042, eq1042⟩ := mod_q t1042; clear t1042
  have key : v1037.toNat + 2 ^ 32 * v1042.toNat + 2 ^ 64 * (q1022 + q1024 + q1026 + q1028 + q1030 + q1035 + q1040 + q1042) = ((v1034.toNat + 2 ^ 32 * v1036.toNat) + (v1010.toNat + 2 ^ 32 * v1014.toNat) + (v1017.toNat + 2 ^ 32 * v1020.toNat) + (v1011.toNat + 2 ^ 32 * v1013.toNat) + (v1015.toNat + 2 ^ 32 * v1018.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v1010.toNat = n1010 at *
    generalize v1011.toNat = n1011 at *
    generalize v1013.toNat = n1013 at *
    generalize v1014.toNat = n1014 at *
    generalize v1015.toNat = n1015 at *
    generalize v1017.toNat = n1017 at *
    generalize v1018.toNat = n1018 at *
    generalize v1020.toNat = n1020 at *
    generalize v1021.toNat = n1021 at *
    generalize v1022.toNat = n1022 at *
    generalize v1023.toNat = n1023 at *
    generalize v1024.toNat = n1024 at *
    generalize v1025.toNat = n1025 at *
    generalize v1026.toNat = n1026 at *
    generalize v1027.toNat = n1027 at *
    generalize v1028.toNat = n1028 at *
    generalize v1029.toNat = n1029 at *
    generalize v1030.toNat = n1030 at *
    generalize v1031.toNat = n1031 at *
    generalize v1034.toNat = n1034 at *
    generalize v1035.toNat = n1035 at *
    generalize v1036.toNat = n1036 at *
    generalize v1037.toNat = n1037 at *
    generalize v1040.toNat = n1040 at *
    generalize v1041.toNat = n1041 at *
    generalize v1042.toNat = n1042 at *
    omega
  exact smm_key key (smm_lt v1037 v1042)

theorem smm_v_R2 {v1037 v1042 v1125 : Word}
    (t1125 : v1125.toNat = v1037.toNat % 2 ^ 29) :
    v1125.toNat = (v1037.toNat + 2 ^ 32 * v1042.toNat) % 2 ^ 29 := by
  have := v1037.isLt; have := v1042.isLt; have := v1125.isLt
  generalize v1037.toNat = n1037 at *
  generalize v1042.toNat = n1042 at *
  generalize v1125.toNat = n1125 at *
  omega

theorem smm_v_C11 {v1037 v1042 v1051 v1054 v1056 v1058 : Word}
    (t1051 : v1051.toNat = v1042.toNat * 2 ^ 3 % 2 ^ 32)
    (t1054 : v1054.toNat = v1037.toNat / 2 ^ 29)
    (t1056 : v1056.toNat = v1054.toNat + v1051.toNat)
    (t1058 : v1058.toNat = v1042.toNat / 2 ^ 29) :
    v1056.toNat + 2 ^ 32 * v1058.toNat = (v1037.toNat + 2 ^ 32 * v1042.toNat) / 2 ^ 29 := by
  have := v1037.isLt; have := v1042.isLt; have := v1051.isLt; have := v1054.isLt; have := v1056.isLt; have := v1058.isLt
  generalize v1037.toNat = n1037 at *
  generalize v1042.toNat = n1042 at *
  generalize v1051.toNat = n1051 at *
  generalize v1054.toNat = n1054 at *
  generalize v1056.toNat = n1056 at *
  generalize v1058.toNat = n1058 at *
  omega

theorem smm_v_PN4L8 {v450 v455 v470 v472 v1044 v1045 : Word}
    (t455 : v455.toNat = v450.toNat * 307527195 % 2 ^ 32)
    (t1044 : v1044.toNat = v455.toNat * 2 ^ 20 % 2 ^ 32)
    (t1045 : v1045.toNat = v470.toNat / 2 ^ 12)
    (wN4 : v470.toNat = ((v450.toNat + 2 ^ 32 * v472.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1044.toNat + 2 ^ 32 * v1045.toNat = v470.toNat * 1048576 := by
  have := v450.isLt; have := v455.isLt; have := v470.isLt; have := v472.isLt; have := v1044.isLt; have := v1045.isLt
  generalize v450.toNat = n450 at *
  generalize v455.toNat = n455 at *
  generalize v470.toNat = n470 at *
  generalize v472.toNat = n472 at *
  generalize v1044.toNat = n1044 at *
  generalize v1045.toNat = n1045 at *
  omega

theorem smm_v_PN8L4 {v843 v1038 v1039 : Word}
    (t1038 : v1038.toNat = v843.toNat * 333 % 2 ^ 32)
    (t1039 : v1039.toNat = v843.toNat * 333 / 2 ^ 32) :
    v1038.toNat + 2 ^ 32 * v1039.toNat = v843.toNat * 333 := by
  have := v843.isLt; have := v1038.isLt; have := v1039.isLt
  generalize v843.toNat = n843 at *
  generalize v1038.toNat = n1038 at *
  generalize v1039.toNat = n1039 at *
  omega

theorem smm_v_S12 {v739 v830 v1038 v1039 v1044 v1045 v1046 v1048 v1049 v1050 v1052 v1053 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 : Word}
    (t1048 : v1048.toNat = (v1045.toNat + v739.toNat) % 2 ^ 32)
    (t1049 : v1046.toNat + 2 ^ 32 * v1049.toNat = v1044.toNat + v830.toNat)
    (t1050 : v1050.toNat = (v1048.toNat + v1049.toNat) % 2 ^ 32)
    (t1052 : v1052.toNat = (v1050.toNat + v1039.toNat) % 2 ^ 32)
    (t1055 : v1053.toNat + 2 ^ 32 * v1055.toNat = v1038.toNat + v1046.toNat)
    (t1057 : v1057.toNat = (v1055.toNat + v1052.toNat) % 2 ^ 32)
    (t1060 : v1060.toNat = (v1058.toNat + v1057.toNat) % 2 ^ 32)
    (t1061 : v1059.toNat + 2 ^ 32 * v1061.toNat = v1053.toNat + v1056.toNat)
    (t1062 : v1062.toNat = (v1060.toNat + v1061.toNat) % 2 ^ 32) :
    v1059.toNat + 2 ^ 32 * v1062.toNat = ((v1056.toNat + 2 ^ 32 * v1058.toNat) + (v830.toNat + 2 ^ 32 * v739.toNat) + (v1044.toNat + 2 ^ 32 * v1045.toNat) + (v1038.toNat + 2 ^ 32 * v1039.toNat)) % 2 ^ 64 := by
  obtain ⟨q1048, eq1048⟩ := mod_q t1048; clear t1048
  obtain ⟨q1050, eq1050⟩ := mod_q t1050; clear t1050
  obtain ⟨q1052, eq1052⟩ := mod_q t1052; clear t1052
  obtain ⟨q1057, eq1057⟩ := mod_q t1057; clear t1057
  obtain ⟨q1060, eq1060⟩ := mod_q t1060; clear t1060
  obtain ⟨q1062, eq1062⟩ := mod_q t1062; clear t1062
  have key : v1059.toNat + 2 ^ 32 * v1062.toNat + 2 ^ 64 * (q1048 + q1050 + q1052 + q1057 + q1060 + q1062) = ((v1056.toNat + 2 ^ 32 * v1058.toNat) + (v830.toNat + 2 ^ 32 * v739.toNat) + (v1044.toNat + 2 ^ 32 * v1045.toNat) + (v1038.toNat + 2 ^ 32 * v1039.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v739.toNat = n739 at *
    generalize v830.toNat = n830 at *
    generalize v1038.toNat = n1038 at *
    generalize v1039.toNat = n1039 at *
    generalize v1044.toNat = n1044 at *
    generalize v1045.toNat = n1045 at *
    generalize v1046.toNat = n1046 at *
    generalize v1048.toNat = n1048 at *
    generalize v1049.toNat = n1049 at *
    generalize v1050.toNat = n1050 at *
    generalize v1052.toNat = n1052 at *
    generalize v1053.toNat = n1053 at *
    generalize v1055.toNat = n1055 at *
    generalize v1056.toNat = n1056 at *
    generalize v1057.toNat = n1057 at *
    generalize v1058.toNat = n1058 at *
    generalize v1059.toNat = n1059 at *
    generalize v1060.toNat = n1060 at *
    generalize v1061.toNat = n1061 at *
    generalize v1062.toNat = n1062 at *
    omega
  exact smm_key key (smm_lt v1059 v1062)

theorem smm_v_R3 {v1059 v1062 v1126 : Word}
    (t1126 : v1126.toNat = v1059.toNat % 2 ^ 29) :
    v1126.toNat = (v1059.toNat + 2 ^ 32 * v1062.toNat) % 2 ^ 29 := by
  have := v1059.isLt; have := v1062.isLt; have := v1126.isLt
  generalize v1059.toNat = n1059 at *
  generalize v1062.toNat = n1062 at *
  generalize v1126.toNat = n1126 at *
  omega

theorem smm_v_C12 {v1059 v1062 v1063 v1069 v1071 v1073 : Word}
    (t1063 : v1063.toNat = v1062.toNat * 2 ^ 3 % 2 ^ 32)
    (t1069 : v1069.toNat = v1059.toNat / 2 ^ 29)
    (t1071 : v1071.toNat = v1069.toNat + v1063.toNat)
    (t1073 : v1073.toNat = v1062.toNat / 2 ^ 29) :
    v1071.toNat + 2 ^ 32 * v1073.toNat = (v1059.toNat + 2 ^ 32 * v1062.toNat) / 2 ^ 29 := by
  have := v1059.isLt; have := v1062.isLt; have := v1063.isLt; have := v1069.isLt; have := v1071.isLt; have := v1073.isLt
  generalize v1059.toNat = n1059 at *
  generalize v1062.toNat = n1062 at *
  generalize v1063.toNat = n1063 at *
  generalize v1069.toNat = n1069 at *
  generalize v1071.toNat = n1071 at *
  generalize v1073.toNat = n1073 at *
  omega

theorem smm_v_PN5L8 {v505 v507 v517 v523 v1064 v1066 : Word}
    (t507 : v507.toNat = v505.toNat * 307527195 % 2 ^ 32)
    (t1064 : v1064.toNat = v523.toNat / 2 ^ 12)
    (t1066 : v1066.toNat = v507.toNat * 2 ^ 20 % 2 ^ 32)
    (wN5 : v523.toNat = ((v505.toNat + 2 ^ 32 * v517.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1066.toNat + 2 ^ 32 * v1064.toNat = v523.toNat * 1048576 := by
  have := v505.isLt; have := v507.isLt; have := v517.isLt; have := v523.isLt; have := v1064.isLt; have := v1066.isLt
  generalize v505.toNat = n505 at *
  generalize v507.toNat = n507 at *
  generalize v517.toNat = n517 at *
  generalize v523.toNat = n523 at *
  generalize v1064.toNat = n1064 at *
  generalize v1066.toNat = n1066 at *
  omega

theorem smm_v_S13 {v272 v278 v1064 v1066 v1067 v1068 v1070 v1071 v1072 v1073 v1074 v1075 v1076 v1077 : Word}
    (t1068 : v1068.toNat = (v1064.toNat + v278.toNat) % 2 ^ 32)
    (t1070 : v1067.toNat + 2 ^ 32 * v1070.toNat = v1066.toNat + v272.toNat)
    (t1072 : v1072.toNat = (v1068.toNat + v1070.toNat) % 2 ^ 32)
    (t1075 : v1075.toNat = (v1072.toNat + v1073.toNat) % 2 ^ 32)
    (t1076 : v1074.toNat + 2 ^ 32 * v1076.toNat = v1067.toNat + v1071.toNat)
    (t1077 : v1077.toNat = (v1076.toNat + v1075.toNat) % 2 ^ 32) :
    v1074.toNat + 2 ^ 32 * v1077.toNat = ((v1071.toNat + 2 ^ 32 * v1073.toNat) + (v272.toNat + 2 ^ 32 * v278.toNat) + (v1066.toNat + 2 ^ 32 * v1064.toNat)) % 2 ^ 64 := by
  obtain ⟨q1068, eq1068⟩ := mod_q t1068; clear t1068
  obtain ⟨q1072, eq1072⟩ := mod_q t1072; clear t1072
  obtain ⟨q1075, eq1075⟩ := mod_q t1075; clear t1075
  obtain ⟨q1077, eq1077⟩ := mod_q t1077; clear t1077
  have key : v1074.toNat + 2 ^ 32 * v1077.toNat + 2 ^ 64 * (q1068 + q1072 + q1075 + q1077) = ((v1071.toNat + 2 ^ 32 * v1073.toNat) + (v272.toNat + 2 ^ 32 * v278.toNat) + (v1066.toNat + 2 ^ 32 * v1064.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v272.toNat = n272 at *
    generalize v278.toNat = n278 at *
    generalize v1064.toNat = n1064 at *
    generalize v1066.toNat = n1066 at *
    generalize v1067.toNat = n1067 at *
    generalize v1068.toNat = n1068 at *
    generalize v1070.toNat = n1070 at *
    generalize v1071.toNat = n1071 at *
    generalize v1072.toNat = n1072 at *
    generalize v1073.toNat = n1073 at *
    generalize v1074.toNat = n1074 at *
    generalize v1075.toNat = n1075 at *
    generalize v1076.toNat = n1076 at *
    generalize v1077.toNat = n1077 at *
    omega
  exact smm_key key (smm_lt v1074 v1077)

theorem smm_v_R4 {v1074 v1077 v1127 : Word}
    (t1127 : v1127.toNat = v1074.toNat % 2 ^ 29) :
    v1127.toNat = (v1074.toNat + 2 ^ 32 * v1077.toNat) % 2 ^ 29 := by
  have := v1074.isLt; have := v1077.isLt; have := v1127.isLt
  generalize v1074.toNat = n1074 at *
  generalize v1077.toNat = n1077 at *
  generalize v1127.toNat = n1127 at *
  omega

theorem smm_v_C13 {v1074 v1077 v1078 v1084 v1086 v1088 : Word}
    (t1078 : v1078.toNat = v1077.toNat * 2 ^ 3 % 2 ^ 32)
    (t1084 : v1084.toNat = v1074.toNat / 2 ^ 29)
    (t1086 : v1086.toNat = v1084.toNat + v1078.toNat)
    (t1088 : v1088.toNat = v1077.toNat / 2 ^ 29) :
    v1086.toNat + 2 ^ 32 * v1088.toNat = (v1074.toNat + 2 ^ 32 * v1077.toNat) / 2 ^ 29 := by
  have := v1074.isLt; have := v1077.isLt; have := v1078.isLt; have := v1084.isLt; have := v1086.isLt; have := v1088.isLt
  generalize v1074.toNat = n1074 at *
  generalize v1077.toNat = n1077 at *
  generalize v1078.toNat = n1078 at *
  generalize v1084.toNat = n1084 at *
  generalize v1086.toNat = n1086 at *
  generalize v1088.toNat = n1088 at *
  omega

theorem smm_v_PN6L8 {v635 v645 v662 v674 v1079 v1081 : Word}
    (t645 : v645.toNat = v635.toNat * 307527195 % 2 ^ 32)
    (t1079 : v1079.toNat = v662.toNat / 2 ^ 12)
    (t1081 : v1081.toNat = v645.toNat * 2 ^ 20 % 2 ^ 32)
    (wN6 : v662.toNat = ((v635.toNat + 2 ^ 32 * v674.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1081.toNat + 2 ^ 32 * v1079.toNat = v662.toNat * 1048576 := by
  have := v635.isLt; have := v645.isLt; have := v662.isLt; have := v674.isLt; have := v1079.isLt; have := v1081.isLt
  generalize v635.toNat = n635 at *
  generalize v645.toNat = n645 at *
  generalize v662.toNat = n662 at *
  generalize v674.toNat = n674 at *
  generalize v1079.toNat = n1079 at *
  generalize v1081.toNat = n1081 at *
  omega

theorem smm_v_S14 {v274 v280 v1079 v1081 v1082 v1083 v1085 v1086 v1087 v1088 v1089 v1090 v1091 v1092 : Word}
    (t1083 : v1083.toNat = (v1079.toNat + v280.toNat) % 2 ^ 32)
    (t1085 : v1082.toNat + 2 ^ 32 * v1085.toNat = v1081.toNat + v274.toNat)
    (t1087 : v1087.toNat = (v1083.toNat + v1085.toNat) % 2 ^ 32)
    (t1090 : v1090.toNat = (v1088.toNat + v1087.toNat) % 2 ^ 32)
    (t1091 : v1089.toNat + 2 ^ 32 * v1091.toNat = v1082.toNat + v1086.toNat)
    (t1092 : v1092.toNat = (v1090.toNat + v1091.toNat) % 2 ^ 32) :
    v1089.toNat + 2 ^ 32 * v1092.toNat = ((v1086.toNat + 2 ^ 32 * v1088.toNat) + (v274.toNat + 2 ^ 32 * v280.toNat) + (v1081.toNat + 2 ^ 32 * v1079.toNat)) % 2 ^ 64 := by
  obtain ⟨q1083, eq1083⟩ := mod_q t1083; clear t1083
  obtain ⟨q1087, eq1087⟩ := mod_q t1087; clear t1087
  obtain ⟨q1090, eq1090⟩ := mod_q t1090; clear t1090
  obtain ⟨q1092, eq1092⟩ := mod_q t1092; clear t1092
  have key : v1089.toNat + 2 ^ 32 * v1092.toNat + 2 ^ 64 * (q1083 + q1087 + q1090 + q1092) = ((v1086.toNat + 2 ^ 32 * v1088.toNat) + (v274.toNat + 2 ^ 32 * v280.toNat) + (v1081.toNat + 2 ^ 32 * v1079.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v274.toNat = n274 at *
    generalize v280.toNat = n280 at *
    generalize v1079.toNat = n1079 at *
    generalize v1081.toNat = n1081 at *
    generalize v1082.toNat = n1082 at *
    generalize v1083.toNat = n1083 at *
    generalize v1085.toNat = n1085 at *
    generalize v1086.toNat = n1086 at *
    generalize v1087.toNat = n1087 at *
    generalize v1088.toNat = n1088 at *
    generalize v1089.toNat = n1089 at *
    generalize v1090.toNat = n1090 at *
    generalize v1091.toNat = n1091 at *
    generalize v1092.toNat = n1092 at *
    omega
  exact smm_key key (smm_lt v1089 v1092)

theorem smm_v_R5 {v1089 v1092 v1128 : Word}
    (t1128 : v1128.toNat = v1089.toNat % 2 ^ 29) :
    v1128.toNat = (v1089.toNat + 2 ^ 32 * v1092.toNat) % 2 ^ 29 := by
  have := v1089.isLt; have := v1092.isLt; have := v1128.isLt
  generalize v1089.toNat = n1089 at *
  generalize v1092.toNat = n1092 at *
  generalize v1128.toNat = n1128 at *
  omega

theorem smm_v_C14 {v1089 v1092 v1093 v1099 v1101 v1103 : Word}
    (t1093 : v1093.toNat = v1092.toNat * 2 ^ 3 % 2 ^ 32)
    (t1099 : v1099.toNat = v1089.toNat / 2 ^ 29)
    (t1101 : v1101.toNat = v1099.toNat + v1093.toNat)
    (t1103 : v1103.toNat = v1092.toNat / 2 ^ 29) :
    v1101.toNat + 2 ^ 32 * v1103.toNat = (v1089.toNat + 2 ^ 32 * v1092.toNat) / 2 ^ 29 := by
  have := v1089.isLt; have := v1092.isLt; have := v1093.isLt; have := v1099.isLt; have := v1101.isLt; have := v1103.isLt
  generalize v1089.toNat = n1089 at *
  generalize v1092.toNat = n1092 at *
  generalize v1093.toNat = n1093 at *
  generalize v1099.toNat = n1099 at *
  generalize v1101.toNat = n1101 at *
  generalize v1103.toNat = n1103 at *
  omega

theorem smm_v_PN7L8 {v730 v733 v747 v750 v1094 v1096 : Word}
    (t733 : v733.toNat = v730.toNat * 307527195 % 2 ^ 32)
    (t1094 : v1094.toNat = v747.toNat / 2 ^ 12)
    (t1096 : v1096.toNat = v733.toNat * 2 ^ 20 % 2 ^ 32)
    (wN7 : v747.toNat = ((v730.toNat + 2 ^ 32 * v750.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1096.toNat + 2 ^ 32 * v1094.toNat = v747.toNat * 1048576 := by
  have := v730.isLt; have := v733.isLt; have := v747.isLt; have := v750.isLt; have := v1094.isLt; have := v1096.isLt
  generalize v730.toNat = n730 at *
  generalize v733.toNat = n733 at *
  generalize v747.toNat = n747 at *
  generalize v750.toNat = n750 at *
  generalize v1094.toNat = n1094 at *
  generalize v1096.toNat = n1096 at *
  omega

theorem smm_v_S15 {v314 v322 v1094 v1096 v1097 v1098 v1100 v1101 v1102 v1103 v1104 v1105 v1106 v1107 : Word}
    (t1098 : v1098.toNat = (v1094.toNat + v322.toNat) % 2 ^ 32)
    (t1100 : v1097.toNat + 2 ^ 32 * v1100.toNat = v1096.toNat + v314.toNat)
    (t1102 : v1102.toNat = (v1098.toNat + v1100.toNat) % 2 ^ 32)
    (t1105 : v1105.toNat = (v1103.toNat + v1102.toNat) % 2 ^ 32)
    (t1106 : v1104.toNat + 2 ^ 32 * v1106.toNat = v1097.toNat + v1101.toNat)
    (t1107 : v1107.toNat = (v1105.toNat + v1106.toNat) % 2 ^ 32) :
    v1104.toNat + 2 ^ 32 * v1107.toNat = ((v1101.toNat + 2 ^ 32 * v1103.toNat) + (v314.toNat + 2 ^ 32 * v322.toNat) + (v1096.toNat + 2 ^ 32 * v1094.toNat)) % 2 ^ 64 := by
  obtain ⟨q1098, eq1098⟩ := mod_q t1098; clear t1098
  obtain ⟨q1102, eq1102⟩ := mod_q t1102; clear t1102
  obtain ⟨q1105, eq1105⟩ := mod_q t1105; clear t1105
  obtain ⟨q1107, eq1107⟩ := mod_q t1107; clear t1107
  have key : v1104.toNat + 2 ^ 32 * v1107.toNat + 2 ^ 64 * (q1098 + q1102 + q1105 + q1107) = ((v1101.toNat + 2 ^ 32 * v1103.toNat) + (v314.toNat + 2 ^ 32 * v322.toNat) + (v1096.toNat + 2 ^ 32 * v1094.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v314.toNat = n314 at *
    generalize v322.toNat = n322 at *
    generalize v1094.toNat = n1094 at *
    generalize v1096.toNat = n1096 at *
    generalize v1097.toNat = n1097 at *
    generalize v1098.toNat = n1098 at *
    generalize v1100.toNat = n1100 at *
    generalize v1101.toNat = n1101 at *
    generalize v1102.toNat = n1102 at *
    generalize v1103.toNat = n1103 at *
    generalize v1104.toNat = n1104 at *
    generalize v1105.toNat = n1105 at *
    generalize v1106.toNat = n1106 at *
    generalize v1107.toNat = n1107 at *
    omega
  exact smm_key key (smm_lt v1104 v1107)

theorem smm_v_R6 {v1104 v1107 v1129 : Word}
    (t1129 : v1129.toNat = v1104.toNat % 2 ^ 29) :
    v1129.toNat = (v1104.toNat + 2 ^ 32 * v1107.toNat) % 2 ^ 29 := by
  have := v1104.isLt; have := v1107.isLt; have := v1129.isLt
  generalize v1104.toNat = n1104 at *
  generalize v1107.toNat = n1107 at *
  generalize v1129.toNat = n1129 at *
  omega

theorem smm_v_C15 {v1104 v1107 v1108 v1113 v1115 v1117 : Word}
    (t1108 : v1108.toNat = v1107.toNat * 2 ^ 3 % 2 ^ 32)
    (t1113 : v1113.toNat = v1104.toNat / 2 ^ 29)
    (t1115 : v1115.toNat = v1113.toNat + v1108.toNat)
    (t1117 : v1117.toNat = v1107.toNat / 2 ^ 29) :
    v1115.toNat + 2 ^ 32 * v1117.toNat = (v1104.toNat + 2 ^ 32 * v1107.toNat) / 2 ^ 29 := by
  have := v1104.isLt; have := v1107.isLt; have := v1108.isLt; have := v1113.isLt; have := v1115.isLt; have := v1117.isLt
  generalize v1104.toNat = n1104 at *
  generalize v1107.toNat = n1107 at *
  generalize v1108.toNat = n1108 at *
  generalize v1113.toNat = n1113 at *
  generalize v1115.toNat = n1115 at *
  generalize v1117.toNat = n1117 at *
  omega

theorem smm_v_PN8L8 {v825 v827 v843 v847 v1109 v1110 : Word}
    (t827 : v827.toNat = v825.toNat * 307527195 % 2 ^ 32)
    (t1109 : v1109.toNat = v843.toNat / 2 ^ 12)
    (t1110 : v1110.toNat = v827.toNat * 2 ^ 20 % 2 ^ 32)
    (wN8 : v843.toNat = ((v825.toNat + 2 ^ 32 * v847.toNat) % 2 ^ 32 * 307527195 % 2 ^ 32) % 2 ^ 29) :
    v1110.toNat + 2 ^ 32 * v1109.toNat = v843.toNat * 1048576 := by
  have := v825.isLt; have := v827.isLt; have := v843.isLt; have := v847.isLt; have := v1109.isLt; have := v1110.isLt
  generalize v825.toNat = n825 at *
  generalize v827.toNat = n827 at *
  generalize v843.toNat = n843 at *
  generalize v847.toNat = n847 at *
  generalize v1109.toNat = n1109 at *
  generalize v1110.toNat = n1110 at *
  omega

theorem smm_v_S16 {v384 v386 v1109 v1110 v1111 v1112 v1114 v1115 v1116 v1117 v1118 v1119 v1120 v1121 : Word}
    (t1112 : v1112.toNat = (v1109.toNat + v384.toNat) % 2 ^ 32)
    (t1114 : v1111.toNat + 2 ^ 32 * v1114.toNat = v1110.toNat + v386.toNat)
    (t1116 : v1116.toNat = (v1114.toNat + v1112.toNat) % 2 ^ 32)
    (t1119 : v1119.toNat = (v1117.toNat + v1116.toNat) % 2 ^ 32)
    (t1120 : v1118.toNat + 2 ^ 32 * v1120.toNat = v1115.toNat + v1111.toNat)
    (t1121 : v1121.toNat = (v1119.toNat + v1120.toNat) % 2 ^ 32) :
    v1118.toNat + 2 ^ 32 * v1121.toNat = ((v1115.toNat + 2 ^ 32 * v1117.toNat) + (v386.toNat + 2 ^ 32 * v384.toNat) + (v1110.toNat + 2 ^ 32 * v1109.toNat)) % 2 ^ 64 := by
  obtain ⟨q1112, eq1112⟩ := mod_q t1112; clear t1112
  obtain ⟨q1116, eq1116⟩ := mod_q t1116; clear t1116
  obtain ⟨q1119, eq1119⟩ := mod_q t1119; clear t1119
  obtain ⟨q1121, eq1121⟩ := mod_q t1121; clear t1121
  have key : v1118.toNat + 2 ^ 32 * v1121.toNat + 2 ^ 64 * (q1112 + q1116 + q1119 + q1121) = ((v1115.toNat + 2 ^ 32 * v1117.toNat) + (v386.toNat + 2 ^ 32 * v384.toNat) + (v1110.toNat + 2 ^ 32 * v1109.toNat)) + 2 ^ 64 * (0) := by
    skip
    generalize v384.toNat = n384 at *
    generalize v386.toNat = n386 at *
    generalize v1109.toNat = n1109 at *
    generalize v1110.toNat = n1110 at *
    generalize v1111.toNat = n1111 at *
    generalize v1112.toNat = n1112 at *
    generalize v1114.toNat = n1114 at *
    generalize v1115.toNat = n1115 at *
    generalize v1116.toNat = n1116 at *
    generalize v1117.toNat = n1117 at *
    generalize v1118.toNat = n1118 at *
    generalize v1119.toNat = n1119 at *
    generalize v1120.toNat = n1120 at *
    generalize v1121.toNat = n1121 at *
    omega
  exact smm_key key (smm_lt v1118 v1121)

theorem smm_v_R7 {v1118 v1121 v1130 : Word}
    (t1130 : v1130.toNat = v1118.toNat % 2 ^ 29) :
    v1130.toNat = (v1118.toNat + 2 ^ 32 * v1121.toNat) % 2 ^ 29 := by
  have := v1118.isLt; have := v1121.isLt; have := v1130.isLt
  generalize v1118.toNat = n1118 at *
  generalize v1121.toNat = n1121 at *
  generalize v1130.toNat = n1130 at *
  omega

theorem smm_v_R8 {v1118 v1121 v1131 v1132 v1133 : Word}
    (t1131 : v1131.toNat = v1121.toNat * 2 ^ 3 % 2 ^ 32)
    (t1132 : v1132.toNat = v1118.toNat / 2 ^ 29)
    (t1133 : v1133.toNat = v1132.toNat + v1131.toNat) :
    v1133.toNat = ((v1118.toNat + 2 ^ 32 * v1121.toNat) / 2 ^ 29) % 2 ^ 32 := by
  have := v1118.isLt; have := v1121.isLt; have := v1131.isLt; have := v1132.isLt; have := v1133.isLt
  generalize v1118.toNat = n1118 at *
  generalize v1121.toNat = n1121 at *
  generalize v1131.toNat = n1131 at *
  generalize v1132.toNat = n1132 at *
  generalize v1133.toNat = n1133 at *
  omega

end C3.RV32
