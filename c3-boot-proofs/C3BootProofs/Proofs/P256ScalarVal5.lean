import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, values, part 5

Each lemma proves one value the code holds in words from its instructions' facts. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

theorem psm_v_VM4 {v792 v841 v844 v846 v847 : Word}
    (t844 : v844.toNat = 4294967295)
    (t846 : v846.toNat + v844.toNat + v841.toNat / 4294967295 = v792.toNat + 2 ^ 32 * (v847.toNat / 4294967295))
    (t847 : v847.toNat = 0 ∨ v847.toNat = 4294967295)
    (t841 : v841.toNat = 0 ∨ v841.toNat = 4294967295) :
    v847.toNat = 4294967295 * (1 - (v792.toNat + 2 ^ 32 - 4294967295 - v841.toNat / 4294967295) / 2 ^ 32) := by
  have := v792.isLt; have := v841.isLt; have := v844.isLt; have := v846.isLt; have := v847.isLt
  generalize v792.toNat = n792 at *
  generalize v841.toNat = n841 at *
  generalize v844.toNat = n844 at *
  generalize v846.toNat = n846 at *
  generalize v847.toNat = n847 at *
  first
    | omega
    | (rcases t847 with _ | _ <;> rcases t841 with _ | _ <;> omega)

theorem psm_v_VD5 {v798 v847 v850 v852 v853 : Word}
    (t850 : v850.toNat = 4294967295)
    (t852 : v852.toNat + v850.toNat + v847.toNat / 4294967295 = v798.toNat + 2 ^ 32 * (v853.toNat / 4294967295))
    (t853 : v853.toNat = 0 ∨ v853.toNat = 4294967295)
    (t847 : v847.toNat = 0 ∨ v847.toNat = 4294967295) :
    v852.toNat = (v798.toNat + 2 ^ 32 - 4294967295 - v847.toNat / 4294967295) % 2 ^ 32 := by
  have := v798.isLt; have := v847.isLt; have := v850.isLt; have := v852.isLt; have := v853.isLt
  generalize v798.toNat = n798 at *
  generalize v847.toNat = n847 at *
  generalize v850.toNat = n850 at *
  generalize v852.toNat = n852 at *
  generalize v853.toNat = n853 at *
  first
    | omega
    | (rcases t853 with _ | _ <;> rcases t847 with _ | _ <;> omega)

theorem psm_v_VM5 {v798 v847 v850 v852 v853 : Word}
    (t850 : v850.toNat = 4294967295)
    (t852 : v852.toNat + v850.toNat + v847.toNat / 4294967295 = v798.toNat + 2 ^ 32 * (v853.toNat / 4294967295))
    (t853 : v853.toNat = 0 ∨ v853.toNat = 4294967295)
    (t847 : v847.toNat = 0 ∨ v847.toNat = 4294967295) :
    v853.toNat = 4294967295 * (1 - (v798.toNat + 2 ^ 32 - 4294967295 - v847.toNat / 4294967295) / 2 ^ 32) := by
  have := v798.isLt; have := v847.isLt; have := v850.isLt; have := v852.isLt; have := v853.isLt
  generalize v798.toNat = n798 at *
  generalize v847.toNat = n847 at *
  generalize v850.toNat = n850 at *
  generalize v852.toNat = n852 at *
  generalize v853.toNat = n853 at *
  first
    | omega
    | (rcases t853 with _ | _ <;> rcases t847 with _ | _ <;> omega)

theorem psm_v_VD6 {v804 v853 v857 v858 v859 : Word}
    (t857 : v857.toNat = 0)
    (t858 : v858.toNat + v857.toNat + v853.toNat / 4294967295 = v804.toNat + 2 ^ 32 * (v859.toNat / 4294967295))
    (t859 : v859.toNat = 0 ∨ v859.toNat = 4294967295)
    (t853 : v853.toNat = 0 ∨ v853.toNat = 4294967295) :
    v858.toNat = (v804.toNat + 2 ^ 32 - 0 - v853.toNat / 4294967295) % 2 ^ 32 := by
  have := v804.isLt; have := v853.isLt; have := v857.isLt; have := v858.isLt; have := v859.isLt
  generalize v804.toNat = n804 at *
  generalize v853.toNat = n853 at *
  generalize v857.toNat = n857 at *
  generalize v858.toNat = n858 at *
  generalize v859.toNat = n859 at *
  first
    | omega
    | (rcases t859 with _ | _ <;> rcases t853 with _ | _ <;> omega)

theorem psm_v_VM6 {v804 v853 v857 v858 v859 : Word}
    (t857 : v857.toNat = 0)
    (t858 : v858.toNat + v857.toNat + v853.toNat / 4294967295 = v804.toNat + 2 ^ 32 * (v859.toNat / 4294967295))
    (t859 : v859.toNat = 0 ∨ v859.toNat = 4294967295)
    (t853 : v853.toNat = 0 ∨ v853.toNat = 4294967295) :
    v859.toNat = 4294967295 * (1 - (v804.toNat + 2 ^ 32 - 0 - v853.toNat / 4294967295) / 2 ^ 32) := by
  have := v804.isLt; have := v853.isLt; have := v857.isLt; have := v858.isLt; have := v859.isLt
  generalize v804.toNat = n804 at *
  generalize v853.toNat = n853 at *
  generalize v857.toNat = n857 at *
  generalize v858.toNat = n858 at *
  generalize v859.toNat = n859 at *
  first
    | omega
    | (rcases t859 with _ | _ <;> rcases t853 with _ | _ <;> omega)

theorem psm_v_VD7 {v810 v859 v862 v864 v865 : Word}
    (t862 : v862.toNat = 4294967295)
    (t864 : v864.toNat + v862.toNat + v859.toNat / 4294967295 = v810.toNat + 2 ^ 32 * (v865.toNat / 4294967295))
    (t865 : v865.toNat = 0 ∨ v865.toNat = 4294967295)
    (t859 : v859.toNat = 0 ∨ v859.toNat = 4294967295) :
    v864.toNat = (v810.toNat + 2 ^ 32 - 4294967295 - v859.toNat / 4294967295) % 2 ^ 32 := by
  have := v810.isLt; have := v859.isLt; have := v862.isLt; have := v864.isLt; have := v865.isLt
  generalize v810.toNat = n810 at *
  generalize v859.toNat = n859 at *
  generalize v862.toNat = n862 at *
  generalize v864.toNat = n864 at *
  generalize v865.toNat = n865 at *
  first
    | omega
    | (rcases t865 with _ | _ <;> rcases t859 with _ | _ <;> omega)

theorem psm_v_VM7 {v810 v859 v862 v864 v865 : Word}
    (t862 : v862.toNat = 4294967295)
    (t864 : v864.toNat + v862.toNat + v859.toNat / 4294967295 = v810.toNat + 2 ^ 32 * (v865.toNat / 4294967295))
    (t865 : v865.toNat = 0 ∨ v865.toNat = 4294967295)
    (t859 : v859.toNat = 0 ∨ v859.toNat = 4294967295) :
    v865.toNat = 4294967295 * (1 - (v810.toNat + 2 ^ 32 - 4294967295 - v859.toNat / 4294967295) / 2 ^ 32) := by
  have := v810.isLt; have := v859.isLt; have := v862.isLt; have := v864.isLt; have := v865.isLt
  generalize v810.toNat = n810 at *
  generalize v859.toNat = n859 at *
  generalize v862.toNat = n862 at *
  generalize v864.toNat = n864 at *
  generalize v865.toNat = n865 at *
  first
    | omega
    | (rcases t865 with _ | _ <;> rcases t859 with _ | _ <;> omega)

theorem psm_v_VD8 {v816 v865 v869 v870 v871 : Word}
    (t869 : v869.toNat = 0)
    (t870 : v870.toNat + v869.toNat + v865.toNat / 4294967295 = v816.toNat + 2 ^ 32 * (v871.toNat / 4294967295))
    (t871 : v871.toNat = 0 ∨ v871.toNat = 4294967295)
    (t865 : v865.toNat = 0 ∨ v865.toNat = 4294967295) :
    v870.toNat = (v816.toNat + 2 ^ 32 - 0 - v865.toNat / 4294967295) % 2 ^ 32 := by
  have := v816.isLt; have := v865.isLt; have := v869.isLt; have := v870.isLt; have := v871.isLt
  generalize v816.toNat = n816 at *
  generalize v865.toNat = n865 at *
  generalize v869.toNat = n869 at *
  generalize v870.toNat = n870 at *
  generalize v871.toNat = n871 at *
  first
    | omega
    | (rcases t871 with _ | _ <;> rcases t865 with _ | _ <;> omega)

theorem psm_v_VM8 {v816 v865 v869 v870 v871 : Word}
    (t869 : v869.toNat = 0)
    (t870 : v870.toNat + v869.toNat + v865.toNat / 4294967295 = v816.toNat + 2 ^ 32 * (v871.toNat / 4294967295))
    (t871 : v871.toNat = 0 ∨ v871.toNat = 4294967295)
    (t865 : v865.toNat = 0 ∨ v865.toNat = 4294967295) :
    v871.toNat = 4294967295 * (1 - (v816.toNat + 2 ^ 32 - 0 - v865.toNat / 4294967295) / 2 ^ 32) := by
  have := v816.isLt; have := v865.isLt; have := v869.isLt; have := v870.isLt; have := v871.isLt
  generalize v816.toNat = n816 at *
  generalize v865.toNat = n865 at *
  generalize v869.toNat = n869 at *
  generalize v870.toNat = n870 at *
  generalize v871.toNat = n871 at *
  first
    | omega
    | (rcases t871 with _ | _ <;> rcases t865 with _ | _ <;> omega)

theorem psm_v_K0 {v871 v872 : Word}
    (t872 : v872.toNat = 4234356049 * (v871.toNat / 4294967295))
    (t871 : v871.toNat = 0 ∨ v871.toNat = 4294967295) :
    v872.toNat = 4234356049 * (v871.toNat / 4294967295) := by
  have := v871.isLt; have := v872.isLt
  generalize v871.toNat = n871 at *
  generalize v872.toNat = n872 at *
  first
    | omega
    | (rcases t871 with _ | _ <;> omega)

theorem psm_v_S123 {v822 v872 v875 v877 : Word}
    (t875 : v875.toNat = (v822.toNat + v872.toNat) % 2 ^ 32)
    (t877 : v875.toNat + 2 ^ 32 * v877.toNat = v822.toNat + v872.toNat) :
    v875.toNat + 2 ^ 32 * v877.toNat = v822.toNat + v872.toNat := by
  have := v822.isLt; have := v872.isLt; have := v875.isLt; have := v877.isLt
  generalize v822.toNat = n822 at *
  generalize v872.toNat = n872 at *
  generalize v875.toNat = n875 at *
  generalize v877.toNat = n877 at *
  first
    | omega
    | (obtain ⟨qt875, et875⟩ := mod_q t875; clear t875; omega)

theorem psm_v_S123l {v822 v872 v875 v877 : Word}
    (t875 : v875.toNat = (v822.toNat + v872.toNat) % 2 ^ 32)
    (wS123 : v875.toNat + 2 ^ 32 * v877.toNat = v822.toNat + v872.toNat) :
    v875.toNat = (v875.toNat + 2 ^ 32 * v877.toNat) % 2 ^ 32 := by
  have := v822.isLt; have := v872.isLt; have := v875.isLt; have := v877.isLt
  generalize v822.toNat = n822 at *
  generalize v872.toNat = n872 at *
  generalize v875.toNat = n875 at *
  generalize v877.toNat = n877 at *
  first
    | omega
    | (obtain ⟨qt875, et875⟩ := mod_q t875; clear t875; omega)

theorem psm_v_S123h {v822 v872 v875 v877 : Word}
    (t877 : v875.toNat + 2 ^ 32 * v877.toNat = v822.toNat + v872.toNat)
    (wS123 : v875.toNat + 2 ^ 32 * v877.toNat = v822.toNat + v872.toNat) :
    v877.toNat = (v875.toNat + 2 ^ 32 * v877.toNat) / 2 ^ 32 := by
  have := v822.isLt; have := v872.isLt; have := v875.isLt; have := v877.isLt
  generalize v822.toNat = n822 at *
  generalize v872.toNat = n872 at *
  generalize v875.toNat = n875 at *
  generalize v877.toNat = n877 at *
  omega

theorem psm_v_K1 {v871 v873 : Word}
    (t873 : v873.toNat = 4089039554 * (v871.toNat / 4294967295))
    (t871 : v871.toNat = 0 ∨ v871.toNat = 4294967295) :
    v873.toNat = 4089039554 * (v871.toNat / 4294967295) := by
  have := v871.isLt; have := v873.isLt
  generalize v871.toNat = n871 at *
  generalize v873.toNat = n873 at *
  first
    | omega
    | (rcases t871 with _ | _ <;> omega)

theorem psm_v_S124 {v828 v873 v876 v877 v879 v880 v881 v883 : Word}
    (t876 : v876.toNat = (v828.toNat + v873.toNat) % 2 ^ 32)
    (t879 : v879.toNat = (v877.toNat + v876.toNat) % 2 ^ 32)
    (t880 : v876.toNat + 2 ^ 32 * v880.toNat = v828.toNat + v873.toNat)
    (t881 : v879.toNat + 2 ^ 32 * v881.toNat = v877.toNat + v876.toNat)
    (t883 : v883.toNat = (v880.toNat + v881.toNat) % 2 ^ 32) :
    v879.toNat + 2 ^ 32 * v883.toNat = v828.toNat + v873.toNat + v877.toNat := by
  have := v828.isLt; have := v873.isLt; have := v876.isLt; have := v877.isLt; have := v879.isLt; have := v880.isLt; have := v881.isLt; have := v883.isLt
  generalize v828.toNat = n828 at *
  generalize v873.toNat = n873 at *
  generalize v876.toNat = n876 at *
  generalize v877.toNat = n877 at *
  generalize v879.toNat = n879 at *
  generalize v880.toNat = n880 at *
  generalize v881.toNat = n881 at *
  generalize v883.toNat = n883 at *
  first
    | omega
    | (obtain ⟨qt876, et876⟩ := mod_q t876; clear t876; obtain ⟨qt879, et879⟩ := mod_q t879; clear t879; omega)

theorem psm_v_S124l {v828 v873 v876 v877 v879 v883 : Word}
    (t876 : v876.toNat = (v828.toNat + v873.toNat) % 2 ^ 32)
    (t879 : v879.toNat = (v877.toNat + v876.toNat) % 2 ^ 32)
    (wS124 : v879.toNat + 2 ^ 32 * v883.toNat = v828.toNat + v873.toNat + v877.toNat) :
    v879.toNat = (v879.toNat + 2 ^ 32 * v883.toNat) % 2 ^ 32 := by
  have := v828.isLt; have := v873.isLt; have := v876.isLt; have := v877.isLt; have := v879.isLt; have := v883.isLt
  generalize v828.toNat = n828 at *
  generalize v873.toNat = n873 at *
  generalize v876.toNat = n876 at *
  generalize v877.toNat = n877 at *
  generalize v879.toNat = n879 at *
  generalize v883.toNat = n883 at *
  first
    | omega
    | (obtain ⟨qt876, et876⟩ := mod_q t876; clear t876; obtain ⟨qt879, et879⟩ := mod_q t879; clear t879; omega)

theorem psm_v_S124h {v828 v873 v876 v877 v879 v880 v881 v883 : Word}
    (t876 : v876.toNat = (v828.toNat + v873.toNat) % 2 ^ 32)
    (t880 : v876.toNat + 2 ^ 32 * v880.toNat = v828.toNat + v873.toNat)
    (t881 : v879.toNat + 2 ^ 32 * v881.toNat = v877.toNat + v876.toNat)
    (t883 : v883.toNat = (v880.toNat + v881.toNat) % 2 ^ 32)
    (wS124 : v879.toNat + 2 ^ 32 * v883.toNat = v828.toNat + v873.toNat + v877.toNat) :
    v883.toNat = (v879.toNat + 2 ^ 32 * v883.toNat) / 2 ^ 32 := by
  have := v828.isLt; have := v873.isLt; have := v876.isLt; have := v877.isLt; have := v879.isLt; have := v880.isLt; have := v881.isLt; have := v883.isLt
  generalize v828.toNat = n828 at *
  generalize v873.toNat = n873 at *
  generalize v876.toNat = n876 at *
  generalize v877.toNat = n877 at *
  generalize v879.toNat = n879 at *
  generalize v880.toNat = n880 at *
  generalize v881.toNat = n881 at *
  generalize v883.toNat = n883 at *
  first
    | omega
    | (obtain ⟨qt876, et876⟩ := mod_q t876; clear t876; obtain ⟨qt883, et883⟩ := mod_q t883; clear t883; omega)

theorem psm_v_K2 {v871 v878 : Word}
    (t878 : v878.toNat = 2803342980 * (v871.toNat / 4294967295))
    (t871 : v871.toNat = 0 ∨ v871.toNat = 4294967295) :
    v878.toNat = 2803342980 * (v871.toNat / 4294967295) := by
  have := v871.isLt; have := v878.isLt
  generalize v871.toNat = n871 at *
  generalize v878.toNat = n878 at *
  first
    | omega
    | (rcases t871 with _ | _ <;> omega)

theorem psm_v_S125 {v834 v878 v882 v883 v885 v886 v887 v890 : Word}
    (t882 : v882.toNat = (v834.toNat + v878.toNat) % 2 ^ 32)
    (t885 : v885.toNat = (v883.toNat + v882.toNat) % 2 ^ 32)
    (t886 : v882.toNat + 2 ^ 32 * v886.toNat = v834.toNat + v878.toNat)
    (t887 : v885.toNat + 2 ^ 32 * v887.toNat = v883.toNat + v882.toNat)
    (t890 : v890.toNat = (v886.toNat + v887.toNat) % 2 ^ 32) :
    v885.toNat + 2 ^ 32 * v890.toNat = v834.toNat + v878.toNat + v883.toNat := by
  have := v834.isLt; have := v878.isLt; have := v882.isLt; have := v883.isLt; have := v885.isLt; have := v886.isLt; have := v887.isLt; have := v890.isLt
  generalize v834.toNat = n834 at *
  generalize v878.toNat = n878 at *
  generalize v882.toNat = n882 at *
  generalize v883.toNat = n883 at *
  generalize v885.toNat = n885 at *
  generalize v886.toNat = n886 at *
  generalize v887.toNat = n887 at *
  generalize v890.toNat = n890 at *
  first
    | omega
    | (obtain ⟨qt882, et882⟩ := mod_q t882; clear t882; obtain ⟨qt885, et885⟩ := mod_q t885; clear t885; omega)

theorem psm_v_S125l {v834 v878 v882 v883 v885 v890 : Word}
    (t882 : v882.toNat = (v834.toNat + v878.toNat) % 2 ^ 32)
    (t885 : v885.toNat = (v883.toNat + v882.toNat) % 2 ^ 32)
    (wS125 : v885.toNat + 2 ^ 32 * v890.toNat = v834.toNat + v878.toNat + v883.toNat) :
    v885.toNat = (v885.toNat + 2 ^ 32 * v890.toNat) % 2 ^ 32 := by
  have := v834.isLt; have := v878.isLt; have := v882.isLt; have := v883.isLt; have := v885.isLt; have := v890.isLt
  generalize v834.toNat = n834 at *
  generalize v878.toNat = n878 at *
  generalize v882.toNat = n882 at *
  generalize v883.toNat = n883 at *
  generalize v885.toNat = n885 at *
  generalize v890.toNat = n890 at *
  first
    | omega
    | (obtain ⟨qt882, et882⟩ := mod_q t882; clear t882; obtain ⟨qt885, et885⟩ := mod_q t885; clear t885; omega)

theorem psm_v_S125h {v834 v878 v882 v883 v885 v886 v887 v890 : Word}
    (t882 : v882.toNat = (v834.toNat + v878.toNat) % 2 ^ 32)
    (t886 : v882.toNat + 2 ^ 32 * v886.toNat = v834.toNat + v878.toNat)
    (t887 : v885.toNat + 2 ^ 32 * v887.toNat = v883.toNat + v882.toNat)
    (t890 : v890.toNat = (v886.toNat + v887.toNat) % 2 ^ 32)
    (wS125 : v885.toNat + 2 ^ 32 * v890.toNat = v834.toNat + v878.toNat + v883.toNat) :
    v890.toNat = (v885.toNat + 2 ^ 32 * v890.toNat) / 2 ^ 32 := by
  have := v834.isLt; have := v878.isLt; have := v882.isLt; have := v883.isLt; have := v885.isLt; have := v886.isLt; have := v887.isLt; have := v890.isLt
  generalize v834.toNat = n834 at *
  generalize v878.toNat = n878 at *
  generalize v882.toNat = n882 at *
  generalize v883.toNat = n883 at *
  generalize v885.toNat = n885 at *
  generalize v886.toNat = n886 at *
  generalize v887.toNat = n887 at *
  generalize v890.toNat = n890 at *
  first
    | omega
    | (obtain ⟨qt882, et882⟩ := mod_q t882; clear t882; obtain ⟨qt890, et890⟩ := mod_q t890; clear t890; omega)

theorem psm_v_K3 {v871 v884 : Word}
    (t884 : v884.toNat = 3169254061 * (v871.toNat / 4294967295))
    (t871 : v871.toNat = 0 ∨ v871.toNat = 4294967295) :
    v884.toNat = 3169254061 * (v871.toNat / 4294967295) := by
  have := v871.isLt; have := v884.isLt
  generalize v871.toNat = n871 at *
  generalize v884.toNat = n884 at *
  first
    | omega
    | (rcases t871 with _ | _ <;> omega)

theorem psm_v_S126 {v840 v884 v889 v890 v891 v892 v893 v895 : Word}
    (t889 : v889.toNat = (v840.toNat + v884.toNat) % 2 ^ 32)
    (t891 : v891.toNat = (v890.toNat + v889.toNat) % 2 ^ 32)
    (t892 : v889.toNat + 2 ^ 32 * v892.toNat = v840.toNat + v884.toNat)
    (t893 : v891.toNat + 2 ^ 32 * v893.toNat = v890.toNat + v889.toNat)
    (t895 : v895.toNat = (v893.toNat + v892.toNat) % 2 ^ 32) :
    v891.toNat + 2 ^ 32 * v895.toNat = v840.toNat + v884.toNat + v890.toNat := by
  have := v840.isLt; have := v884.isLt; have := v889.isLt; have := v890.isLt; have := v891.isLt; have := v892.isLt; have := v893.isLt; have := v895.isLt
  generalize v840.toNat = n840 at *
  generalize v884.toNat = n884 at *
  generalize v889.toNat = n889 at *
  generalize v890.toNat = n890 at *
  generalize v891.toNat = n891 at *
  generalize v892.toNat = n892 at *
  generalize v893.toNat = n893 at *
  generalize v895.toNat = n895 at *
  first
    | omega
    | (obtain ⟨qt889, et889⟩ := mod_q t889; clear t889; obtain ⟨qt891, et891⟩ := mod_q t891; clear t891; omega)

theorem psm_v_S126l {v840 v884 v889 v890 v891 v895 : Word}
    (t889 : v889.toNat = (v840.toNat + v884.toNat) % 2 ^ 32)
    (t891 : v891.toNat = (v890.toNat + v889.toNat) % 2 ^ 32)
    (wS126 : v891.toNat + 2 ^ 32 * v895.toNat = v840.toNat + v884.toNat + v890.toNat) :
    v891.toNat = (v891.toNat + 2 ^ 32 * v895.toNat) % 2 ^ 32 := by
  have := v840.isLt; have := v884.isLt; have := v889.isLt; have := v890.isLt; have := v891.isLt; have := v895.isLt
  generalize v840.toNat = n840 at *
  generalize v884.toNat = n884 at *
  generalize v889.toNat = n889 at *
  generalize v890.toNat = n890 at *
  generalize v891.toNat = n891 at *
  generalize v895.toNat = n895 at *
  first
    | omega
    | (obtain ⟨qt889, et889⟩ := mod_q t889; clear t889; obtain ⟨qt891, et891⟩ := mod_q t891; clear t891; omega)

theorem psm_v_S126h {v840 v884 v889 v890 v891 v892 v893 v895 : Word}
    (t889 : v889.toNat = (v840.toNat + v884.toNat) % 2 ^ 32)
    (t892 : v889.toNat + 2 ^ 32 * v892.toNat = v840.toNat + v884.toNat)
    (t893 : v891.toNat + 2 ^ 32 * v893.toNat = v890.toNat + v889.toNat)
    (t895 : v895.toNat = (v893.toNat + v892.toNat) % 2 ^ 32)
    (wS126 : v891.toNat + 2 ^ 32 * v895.toNat = v840.toNat + v884.toNat + v890.toNat) :
    v895.toNat = (v891.toNat + 2 ^ 32 * v895.toNat) / 2 ^ 32 := by
  have := v840.isLt; have := v884.isLt; have := v889.isLt; have := v890.isLt; have := v891.isLt; have := v892.isLt; have := v893.isLt; have := v895.isLt
  generalize v840.toNat = n840 at *
  generalize v884.toNat = n884 at *
  generalize v889.toNat = n889 at *
  generalize v890.toNat = n890 at *
  generalize v891.toNat = n891 at *
  generalize v892.toNat = n892 at *
  generalize v893.toNat = n893 at *
  generalize v895.toNat = n895 at *
  first
    | omega
    | (obtain ⟨qt889, et889⟩ := mod_q t889; clear t889; obtain ⟨qt895, et895⟩ := mod_q t895; clear t895; omega)

theorem psm_v_S127 {v846 v871 v894 v895 v896 v897 v898 v900 : Word}
    (t894 : v894.toNat = (v846.toNat + v871.toNat) % 2 ^ 32)
    (t896 : v896.toNat = (v895.toNat + v894.toNat) % 2 ^ 32)
    (t897 : v894.toNat + 2 ^ 32 * v897.toNat = v846.toNat + v871.toNat)
    (t898 : v896.toNat + 2 ^ 32 * v898.toNat = v895.toNat + v894.toNat)
    (t900 : v900.toNat = (v898.toNat + v897.toNat) % 2 ^ 32) :
    v896.toNat + 2 ^ 32 * v900.toNat = v846.toNat + v871.toNat + v895.toNat := by
  have := v846.isLt; have := v871.isLt; have := v894.isLt; have := v895.isLt; have := v896.isLt; have := v897.isLt; have := v898.isLt; have := v900.isLt
  generalize v846.toNat = n846 at *
  generalize v871.toNat = n871 at *
  generalize v894.toNat = n894 at *
  generalize v895.toNat = n895 at *
  generalize v896.toNat = n896 at *
  generalize v897.toNat = n897 at *
  generalize v898.toNat = n898 at *
  generalize v900.toNat = n900 at *
  first
    | omega
    | (obtain ⟨qt894, et894⟩ := mod_q t894; clear t894; obtain ⟨qt896, et896⟩ := mod_q t896; clear t896; omega)

theorem psm_v_S127l {v846 v871 v894 v895 v896 v900 : Word}
    (t894 : v894.toNat = (v846.toNat + v871.toNat) % 2 ^ 32)
    (t896 : v896.toNat = (v895.toNat + v894.toNat) % 2 ^ 32)
    (wS127 : v896.toNat + 2 ^ 32 * v900.toNat = v846.toNat + v871.toNat + v895.toNat) :
    v896.toNat = (v896.toNat + 2 ^ 32 * v900.toNat) % 2 ^ 32 := by
  have := v846.isLt; have := v871.isLt; have := v894.isLt; have := v895.isLt; have := v896.isLt; have := v900.isLt
  generalize v846.toNat = n846 at *
  generalize v871.toNat = n871 at *
  generalize v894.toNat = n894 at *
  generalize v895.toNat = n895 at *
  generalize v896.toNat = n896 at *
  generalize v900.toNat = n900 at *
  first
    | omega
    | (obtain ⟨qt894, et894⟩ := mod_q t894; clear t894; obtain ⟨qt896, et896⟩ := mod_q t896; clear t896; omega)

theorem psm_v_S127h {v846 v871 v894 v895 v896 v897 v898 v900 : Word}
    (t894 : v894.toNat = (v846.toNat + v871.toNat) % 2 ^ 32)
    (t897 : v894.toNat + 2 ^ 32 * v897.toNat = v846.toNat + v871.toNat)
    (t898 : v896.toNat + 2 ^ 32 * v898.toNat = v895.toNat + v894.toNat)
    (t900 : v900.toNat = (v898.toNat + v897.toNat) % 2 ^ 32)
    (wS127 : v896.toNat + 2 ^ 32 * v900.toNat = v846.toNat + v871.toNat + v895.toNat) :
    v900.toNat = (v896.toNat + 2 ^ 32 * v900.toNat) / 2 ^ 32 := by
  have := v846.isLt; have := v871.isLt; have := v894.isLt; have := v895.isLt; have := v896.isLt; have := v897.isLt; have := v898.isLt; have := v900.isLt
  generalize v846.toNat = n846 at *
  generalize v871.toNat = n871 at *
  generalize v894.toNat = n894 at *
  generalize v895.toNat = n895 at *
  generalize v896.toNat = n896 at *
  generalize v897.toNat = n897 at *
  generalize v898.toNat = n898 at *
  generalize v900.toNat = n900 at *
  first
    | omega
    | (obtain ⟨qt894, et894⟩ := mod_q t894; clear t894; obtain ⟨qt900, et900⟩ := mod_q t900; clear t900; omega)

theorem psm_v_S128 {v852 v871 v899 v900 v901 v902 v903 v904 : Word}
    (t899 : v899.toNat = (v852.toNat + v871.toNat) % 2 ^ 32)
    (t901 : v901.toNat = (v900.toNat + v899.toNat) % 2 ^ 32)
    (t902 : v899.toNat + 2 ^ 32 * v902.toNat = v852.toNat + v871.toNat)
    (t903 : v901.toNat + 2 ^ 32 * v903.toNat = v900.toNat + v899.toNat)
    (t904 : v904.toNat = (v903.toNat + v902.toNat) % 2 ^ 32) :
    v901.toNat + 2 ^ 32 * v904.toNat = v852.toNat + v871.toNat + v900.toNat := by
  have := v852.isLt; have := v871.isLt; have := v899.isLt; have := v900.isLt; have := v901.isLt; have := v902.isLt; have := v903.isLt; have := v904.isLt
  generalize v852.toNat = n852 at *
  generalize v871.toNat = n871 at *
  generalize v899.toNat = n899 at *
  generalize v900.toNat = n900 at *
  generalize v901.toNat = n901 at *
  generalize v902.toNat = n902 at *
  generalize v903.toNat = n903 at *
  generalize v904.toNat = n904 at *
  first
    | omega
    | (obtain ⟨qt899, et899⟩ := mod_q t899; clear t899; obtain ⟨qt901, et901⟩ := mod_q t901; clear t901; omega)

theorem psm_v_S128l {v852 v871 v899 v900 v901 v904 : Word}
    (t899 : v899.toNat = (v852.toNat + v871.toNat) % 2 ^ 32)
    (t901 : v901.toNat = (v900.toNat + v899.toNat) % 2 ^ 32)
    (wS128 : v901.toNat + 2 ^ 32 * v904.toNat = v852.toNat + v871.toNat + v900.toNat) :
    v901.toNat = (v901.toNat + 2 ^ 32 * v904.toNat) % 2 ^ 32 := by
  have := v852.isLt; have := v871.isLt; have := v899.isLt; have := v900.isLt; have := v901.isLt; have := v904.isLt
  generalize v852.toNat = n852 at *
  generalize v871.toNat = n871 at *
  generalize v899.toNat = n899 at *
  generalize v900.toNat = n900 at *
  generalize v901.toNat = n901 at *
  generalize v904.toNat = n904 at *
  first
    | omega
    | (obtain ⟨qt899, et899⟩ := mod_q t899; clear t899; obtain ⟨qt901, et901⟩ := mod_q t901; clear t901; omega)

theorem psm_v_S128h {v852 v871 v899 v900 v901 v902 v903 v904 : Word}
    (t899 : v899.toNat = (v852.toNat + v871.toNat) % 2 ^ 32)
    (t902 : v899.toNat + 2 ^ 32 * v902.toNat = v852.toNat + v871.toNat)
    (t903 : v901.toNat + 2 ^ 32 * v903.toNat = v900.toNat + v899.toNat)
    (t904 : v904.toNat = (v903.toNat + v902.toNat) % 2 ^ 32)
    (wS128 : v901.toNat + 2 ^ 32 * v904.toNat = v852.toNat + v871.toNat + v900.toNat) :
    v904.toNat = (v901.toNat + 2 ^ 32 * v904.toNat) / 2 ^ 32 := by
  have := v852.isLt; have := v871.isLt; have := v899.isLt; have := v900.isLt; have := v901.isLt; have := v902.isLt; have := v903.isLt; have := v904.isLt
  generalize v852.toNat = n852 at *
  generalize v871.toNat = n871 at *
  generalize v899.toNat = n899 at *
  generalize v900.toNat = n900 at *
  generalize v901.toNat = n901 at *
  generalize v902.toNat = n902 at *
  generalize v903.toNat = n903 at *
  generalize v904.toNat = n904 at *
  first
    | omega
    | (obtain ⟨qt899, et899⟩ := mod_q t899; clear t899; obtain ⟨qt904, et904⟩ := mod_q t904; clear t904; omega)

theorem psm_v_S129 {v858 v904 v906 v907 : Word}
    (t906 : v906.toNat = (v858.toNat + v904.toNat) % 2 ^ 32)
    (t907 : v906.toNat + 2 ^ 32 * v907.toNat = v858.toNat + v904.toNat) :
    v906.toNat + 2 ^ 32 * v907.toNat = v858.toNat + v904.toNat := by
  have := v858.isLt; have := v904.isLt; have := v906.isLt; have := v907.isLt
  generalize v858.toNat = n858 at *
  generalize v904.toNat = n904 at *
  generalize v906.toNat = n906 at *
  generalize v907.toNat = n907 at *
  first
    | omega
    | (obtain ⟨qt906, et906⟩ := mod_q t906; clear t906; omega)

theorem psm_v_S129l {v858 v904 v906 v907 : Word}
    (t906 : v906.toNat = (v858.toNat + v904.toNat) % 2 ^ 32)
    (wS129 : v906.toNat + 2 ^ 32 * v907.toNat = v858.toNat + v904.toNat) :
    v906.toNat = (v906.toNat + 2 ^ 32 * v907.toNat) % 2 ^ 32 := by
  have := v858.isLt; have := v904.isLt; have := v906.isLt; have := v907.isLt
  generalize v858.toNat = n858 at *
  generalize v904.toNat = n904 at *
  generalize v906.toNat = n906 at *
  generalize v907.toNat = n907 at *
  first
    | omega
    | (obtain ⟨qt906, et906⟩ := mod_q t906; clear t906; omega)

theorem psm_v_S129h {v858 v904 v906 v907 : Word}
    (t907 : v906.toNat + 2 ^ 32 * v907.toNat = v858.toNat + v904.toNat)
    (wS129 : v906.toNat + 2 ^ 32 * v907.toNat = v858.toNat + v904.toNat) :
    v907.toNat = (v906.toNat + 2 ^ 32 * v907.toNat) / 2 ^ 32 := by
  have := v858.isLt; have := v904.isLt; have := v906.isLt; have := v907.isLt
  generalize v858.toNat = n858 at *
  generalize v904.toNat = n904 at *
  generalize v906.toNat = n906 at *
  generalize v907.toNat = n907 at *
  omega

theorem psm_v_S130l {v864 v871 v905 v907 v913 : Word}
    (t905 : v905.toNat = (v871.toNat + v864.toNat) % 2 ^ 32)
    (t913 : v913.toNat = (v905.toNat + v907.toNat) % 2 ^ 32) :
    v913.toNat = (v864.toNat + v871.toNat + v907.toNat) % 2 ^ 32 := by
  obtain ⟨qt905, eqt905⟩ := mod_q t905; clear t905
  obtain ⟨qt913, eqt913⟩ := mod_q t913; clear t913
  have key : v913.toNat + 2 ^ 32 * (qt905 + qt913) = (v864.toNat + v871.toNat + v907.toNat) + 2 ^ 32 * (0) := by
    skip
    generalize v864.toNat = n864 at *
    generalize v871.toNat = n871 at *
    generalize v905.toNat = n905 at *
    generalize v907.toNat = n907 at *
    generalize v913.toNat = n913 at *
    omega
  exact psm_key32 (key ) v913.isLt

end C3.RV32
