import OMAStatements.S_oeis_a126323
import Mathlib

namespace OMA.S_oeis_a126323

open PowerSeries

lemma bs_sq (T : PowerSeries ℚ) (hT : constantCoeff T = 0) :
    ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst T) * ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst T) = 1 + T := by
  have hs : HasSubst T := HasSubst.of_constantCoeff_zero' hT
  rw [← PowerSeries.subst_mul hs, ← PowerSeries.binomialSeries_add]
  have : ((1 / 2 : ℚ) + 1 / 2) = ((1 : ℕ) : ℚ) := by norm_num
  rw [this, PowerSeries.binomialSeries_nat]
  rw [PowerSeries.subst_pow hs, pow_one]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_X hs]
  have h1 : (1 : PowerSeries ℚ).subst T = 1 := by
    have := PowerSeries.subst_C (a := T) (1 : ℚ)
    simpa using this
  rw [h1]

lemma sqrt_ode (S R : PowerSeries ℚ) (h : S * S = R) :
    2 * R * derivative ℚ S = derivative ℚ R * S := by
  rw [← h, Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

@[simp] lemma dn2 : derivative ℚ (2 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2
@[simp] lemma cc2 : constantCoeff (2 : PowerSeries ℚ) = 2 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2
lemma cm2 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2 : PowerSeries ℚ) * F) = 2 * coeff m F := by
  have e : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat C 2).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3 : derivative ℚ (3 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3
@[simp] lemma cc3 : constantCoeff (3 : PowerSeries ℚ) = 3 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3
lemma cm3 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3 : PowerSeries ℚ) * F) = 3 * coeff m F := by
  have e : (3 : PowerSeries ℚ) = C (3 : ℚ) := (map_ofNat C 3).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4 : derivative ℚ (4 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4
@[simp] lemma cc4 : constantCoeff (4 : PowerSeries ℚ) = 4 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4
lemma cm4 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4 : PowerSeries ℚ) * F) = 4 * coeff m F := by
  have e : (4 : PowerSeries ℚ) = C (4 : ℚ) := (map_ofNat C 4).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5 : derivative ℚ (5 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5
@[simp] lemma cc5 : constantCoeff (5 : PowerSeries ℚ) = 5 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5
lemma cm5 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5 : PowerSeries ℚ) * F) = 5 * coeff m F := by
  have e : (5 : PowerSeries ℚ) = C (5 : ℚ) := (map_ofNat C 5).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6 : derivative ℚ (6 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6
@[simp] lemma cc6 : constantCoeff (6 : PowerSeries ℚ) = 6 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6
lemma cm6 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6 : PowerSeries ℚ) * F) = 6 * coeff m F := by
  have e : (6 : PowerSeries ℚ) = C (6 : ℚ) := (map_ofNat C 6).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7 : derivative ℚ (7 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7
@[simp] lemma cc7 : constantCoeff (7 : PowerSeries ℚ) = 7 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7
lemma cm7 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7 : PowerSeries ℚ) * F) = 7 * coeff m F := by
  have e : (7 : PowerSeries ℚ) = C (7 : ℚ) := (map_ofNat C 7).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8 : derivative ℚ (8 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8
@[simp] lemma cc8 : constantCoeff (8 : PowerSeries ℚ) = 8 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8
lemma cm8 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8 : PowerSeries ℚ) * F) = 8 * coeff m F := by
  have e : (8 : PowerSeries ℚ) = C (8 : ℚ) := (map_ofNat C 8).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9 : derivative ℚ (9 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9
@[simp] lemma cc9 : constantCoeff (9 : PowerSeries ℚ) = 9 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9
lemma cm9 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9 : PowerSeries ℚ) * F) = 9 * coeff m F := by
  have e : (9 : PowerSeries ℚ) = C (9 : ℚ) := (map_ofNat C 9).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10 : derivative ℚ (10 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10
@[simp] lemma cc10 : constantCoeff (10 : PowerSeries ℚ) = 10 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10
lemma cm10 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10 : PowerSeries ℚ) * F) = 10 * coeff m F := by
  have e : (10 : PowerSeries ℚ) = C (10 : ℚ) := (map_ofNat C 10).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11 : derivative ℚ (11 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11
@[simp] lemma cc11 : constantCoeff (11 : PowerSeries ℚ) = 11 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11
lemma cm11 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11 : PowerSeries ℚ) * F) = 11 * coeff m F := by
  have e : (11 : PowerSeries ℚ) = C (11 : ℚ) := (map_ofNat C 11).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn12 : derivative ℚ (12 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 12
@[simp] lemma cc12 : constantCoeff (12 : PowerSeries ℚ) = 12 := by simpa using map_natCast (constantCoeff (R := ℚ)) 12
lemma cm12 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((12 : PowerSeries ℚ) * F) = 12 * coeff m F := by
  have e : (12 : PowerSeries ℚ) = C (12 : ℚ) := (map_ofNat C 12).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn13 : derivative ℚ (13 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 13
@[simp] lemma cc13 : constantCoeff (13 : PowerSeries ℚ) = 13 := by simpa using map_natCast (constantCoeff (R := ℚ)) 13
lemma cm13 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((13 : PowerSeries ℚ) * F) = 13 * coeff m F := by
  have e : (13 : PowerSeries ℚ) = C (13 : ℚ) := (map_ofNat C 13).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14 : derivative ℚ (14 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14
@[simp] lemma cc14 : constantCoeff (14 : PowerSeries ℚ) = 14 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14
lemma cm14 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14 : PowerSeries ℚ) * F) = 14 * coeff m F := by
  have e : (14 : PowerSeries ℚ) = C (14 : ℚ) := (map_ofNat C 14).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15 : derivative ℚ (15 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15
@[simp] lemma cc15 : constantCoeff (15 : PowerSeries ℚ) = 15 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15
lemma cm15 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15 : PowerSeries ℚ) * F) = 15 * coeff m F := by
  have e : (15 : PowerSeries ℚ) = C (15 : ℚ) := (map_ofNat C 15).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16 : derivative ℚ (16 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16
@[simp] lemma cc16 : constantCoeff (16 : PowerSeries ℚ) = 16 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16
lemma cm16 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16 : PowerSeries ℚ) * F) = 16 * coeff m F := by
  have e : (16 : PowerSeries ℚ) = C (16 : ℚ) := (map_ofNat C 16).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18 : derivative ℚ (18 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18
@[simp] lemma cc18 : constantCoeff (18 : PowerSeries ℚ) = 18 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18
lemma cm18 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18 : PowerSeries ℚ) * F) = 18 * coeff m F := by
  have e : (18 : PowerSeries ℚ) = C (18 : ℚ) := (map_ofNat C 18).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn20 : derivative ℚ (20 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20
@[simp] lemma cc20 : constantCoeff (20 : PowerSeries ℚ) = 20 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20
lemma cm20 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20 : PowerSeries ℚ) * F) = 20 * coeff m F := by
  have e : (20 : PowerSeries ℚ) = C (20 : ℚ) := (map_ofNat C 20).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn21 : derivative ℚ (21 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 21
@[simp] lemma cc21 : constantCoeff (21 : PowerSeries ℚ) = 21 := by simpa using map_natCast (constantCoeff (R := ℚ)) 21
lemma cm21 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((21 : PowerSeries ℚ) * F) = 21 * coeff m F := by
  have e : (21 : PowerSeries ℚ) = C (21 : ℚ) := (map_ofNat C 21).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn27 : derivative ℚ (27 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 27
@[simp] lemma cc27 : constantCoeff (27 : PowerSeries ℚ) = 27 := by simpa using map_natCast (constantCoeff (R := ℚ)) 27
lemma cm27 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((27 : PowerSeries ℚ) * F) = 27 * coeff m F := by
  have e : (27 : PowerSeries ℚ) = C (27 : ℚ) := (map_ofNat C 27).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn36 : derivative ℚ (36 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 36
@[simp] lemma cc36 : constantCoeff (36 : PowerSeries ℚ) = 36 := by simpa using map_natCast (constantCoeff (R := ℚ)) 36
lemma cm36 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((36 : PowerSeries ℚ) * F) = 36 * coeff m F := by
  have e : (36 : PowerSeries ℚ) = C (36 : ℚ) := (map_ofNat C 36).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn45 : derivative ℚ (45 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 45
@[simp] lemma cc45 : constantCoeff (45 : PowerSeries ℚ) = 45 := by simpa using map_natCast (constantCoeff (R := ℚ)) 45
lemma cm45 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((45 : PowerSeries ℚ) * F) = 45 * coeff m F := by
  have e : (45 : PowerSeries ℚ) = C (45 : ℚ) := (map_ofNat C 45).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn75 : derivative ℚ (75 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 75
@[simp] lemma cc75 : constantCoeff (75 : PowerSeries ℚ) = 75 := by simpa using map_natCast (constantCoeff (R := ℚ)) 75
lemma cm75 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((75 : PowerSeries ℚ) * F) = 75 * coeff m F := by
  have e : (75 : PowerSeries ℚ) = C (75 : ℚ) := (map_ofNat C 75).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn77 : derivative ℚ (77 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 77
@[simp] lemma cc77 : constantCoeff (77 : PowerSeries ℚ) = 77 := by simpa using map_natCast (constantCoeff (R := ℚ)) 77
lemma cm77 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((77 : PowerSeries ℚ) * F) = 77 * coeff m F := by
  have e : (77 : PowerSeries ℚ) = C (77 : ℚ) := (map_ofNat C 77).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn102 : derivative ℚ (102 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 102
@[simp] lemma cc102 : constantCoeff (102 : PowerSeries ℚ) = 102 := by simpa using map_natCast (constantCoeff (R := ℚ)) 102
lemma cm102 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((102 : PowerSeries ℚ) * F) = 102 * coeff m F := by
  have e : (102 : PowerSeries ℚ) = C (102 : ℚ) := (map_ofNat C 102).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn111 : derivative ℚ (111 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 111
@[simp] lemma cc111 : constantCoeff (111 : PowerSeries ℚ) = 111 := by simpa using map_natCast (constantCoeff (R := ℚ)) 111
lemma cm111 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((111 : PowerSeries ℚ) * F) = 111 * coeff m F := by
  have e : (111 : PowerSeries ℚ) = C (111 : ℚ) := (map_ofNat C 111).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn132 : derivative ℚ (132 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 132
@[simp] lemma cc132 : constantCoeff (132 : PowerSeries ℚ) = 132 := by simpa using map_natCast (constantCoeff (R := ℚ)) 132
lemma cm132 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((132 : PowerSeries ℚ) * F) = 132 * coeff m F := by
  have e : (132 : PowerSeries ℚ) = C (132 : ℚ) := (map_ofNat C 132).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn135 : derivative ℚ (135 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 135
@[simp] lemma cc135 : constantCoeff (135 : PowerSeries ℚ) = 135 := by simpa using map_natCast (constantCoeff (R := ℚ)) 135
lemma cm135 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((135 : PowerSeries ℚ) * F) = 135 * coeff m F := by
  have e : (135 : PowerSeries ℚ) = C (135 : ℚ) := (map_ofNat C 135).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn136 : derivative ℚ (136 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 136
@[simp] lemma cc136 : constantCoeff (136 : PowerSeries ℚ) = 136 := by simpa using map_natCast (constantCoeff (R := ℚ)) 136
lemma cm136 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((136 : PowerSeries ℚ) * F) = 136 * coeff m F := by
  have e : (136 : PowerSeries ℚ) = C (136 : ℚ) := (map_ofNat C 136).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn150 : derivative ℚ (150 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 150
@[simp] lemma cc150 : constantCoeff (150 : PowerSeries ℚ) = 150 := by simpa using map_natCast (constantCoeff (R := ℚ)) 150
lemma cm150 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((150 : PowerSeries ℚ) * F) = 150 * coeff m F := by
  have e : (150 : PowerSeries ℚ) = C (150 : ℚ) := (map_ofNat C 150).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn154 : derivative ℚ (154 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 154
@[simp] lemma cc154 : constantCoeff (154 : PowerSeries ℚ) = 154 := by simpa using map_natCast (constantCoeff (R := ℚ)) 154
lemma cm154 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((154 : PowerSeries ℚ) * F) = 154 * coeff m F := by
  have e : (154 : PowerSeries ℚ) = C (154 : ℚ) := (map_ofNat C 154).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn162 : derivative ℚ (162 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 162
@[simp] lemma cc162 : constantCoeff (162 : PowerSeries ℚ) = 162 := by simpa using map_natCast (constantCoeff (R := ℚ)) 162
lemma cm162 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((162 : PowerSeries ℚ) * F) = 162 * coeff m F := by
  have e : (162 : PowerSeries ℚ) = C (162 : ℚ) := (map_ofNat C 162).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn180 : derivative ℚ (180 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 180
@[simp] lemma cc180 : constantCoeff (180 : PowerSeries ℚ) = 180 := by simpa using map_natCast (constantCoeff (R := ℚ)) 180
lemma cm180 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((180 : PowerSeries ℚ) * F) = 180 * coeff m F := by
  have e : (180 : PowerSeries ℚ) = C (180 : ℚ) := (map_ofNat C 180).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn182 : derivative ℚ (182 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 182
@[simp] lemma cc182 : constantCoeff (182 : PowerSeries ℚ) = 182 := by simpa using map_natCast (constantCoeff (R := ℚ)) 182
lemma cm182 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((182 : PowerSeries ℚ) * F) = 182 * coeff m F := by
  have e : (182 : PowerSeries ℚ) = C (182 : ℚ) := (map_ofNat C 182).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn225 : derivative ℚ (225 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 225
@[simp] lemma cc225 : constantCoeff (225 : PowerSeries ℚ) = 225 := by simpa using map_natCast (constantCoeff (R := ℚ)) 225
lemma cm225 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((225 : PowerSeries ℚ) * F) = 225 * coeff m F := by
  have e : (225 : PowerSeries ℚ) = C (225 : ℚ) := (map_ofNat C 225).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn250 : derivative ℚ (250 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 250
@[simp] lemma cc250 : constantCoeff (250 : PowerSeries ℚ) = 250 := by simpa using map_natCast (constantCoeff (R := ℚ)) 250
lemma cm250 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((250 : PowerSeries ℚ) * F) = 250 * coeff m F := by
  have e : (250 : PowerSeries ℚ) = C (250 : ℚ) := (map_ofNat C 250).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn264 : derivative ℚ (264 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 264
@[simp] lemma cc264 : constantCoeff (264 : PowerSeries ℚ) = 264 := by simpa using map_natCast (constantCoeff (R := ℚ)) 264
lemma cm264 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((264 : PowerSeries ℚ) * F) = 264 * coeff m F := by
  have e : (264 : PowerSeries ℚ) = C (264 : ℚ) := (map_ofNat C 264).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn272 : derivative ℚ (272 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 272
@[simp] lemma cc272 : constantCoeff (272 : PowerSeries ℚ) = 272 := by simpa using map_natCast (constantCoeff (R := ℚ)) 272
lemma cm272 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((272 : PowerSeries ℚ) * F) = 272 * coeff m F := by
  have e : (272 : PowerSeries ℚ) = C (272 : ℚ) := (map_ofNat C 272).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn282 : derivative ℚ (282 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 282
@[simp] lemma cc282 : constantCoeff (282 : PowerSeries ℚ) = 282 := by simpa using map_natCast (constantCoeff (R := ℚ)) 282
lemma cm282 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((282 : PowerSeries ℚ) * F) = 282 * coeff m F := by
  have e : (282 : PowerSeries ℚ) = C (282 : ℚ) := (map_ofNat C 282).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn306 : derivative ℚ (306 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 306
@[simp] lemma cc306 : constantCoeff (306 : PowerSeries ℚ) = 306 := by simpa using map_natCast (constantCoeff (R := ℚ)) 306
lemma cm306 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((306 : PowerSeries ℚ) * F) = 306 * coeff m F := by
  have e : (306 : PowerSeries ℚ) = C (306 : ℚ) := (map_ofNat C 306).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn318 : derivative ℚ (318 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 318
@[simp] lemma cc318 : constantCoeff (318 : PowerSeries ℚ) = 318 := by simpa using map_natCast (constantCoeff (R := ℚ)) 318
lemma cm318 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((318 : PowerSeries ℚ) * F) = 318 * coeff m F := by
  have e : (318 : PowerSeries ℚ) = C (318 : ℚ) := (map_ofNat C 318).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn333 : derivative ℚ (333 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 333
@[simp] lemma cc333 : constantCoeff (333 : PowerSeries ℚ) = 333 := by simpa using map_natCast (constantCoeff (R := ℚ)) 333
lemma cm333 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((333 : PowerSeries ℚ) * F) = 333 * coeff m F := by
  have e : (333 : PowerSeries ℚ) = C (333 : ℚ) := (map_ofNat C 333).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn342 : derivative ℚ (342 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 342
@[simp] lemma cc342 : constantCoeff (342 : PowerSeries ℚ) = 342 := by simpa using map_natCast (constantCoeff (R := ℚ)) 342
lemma cm342 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((342 : PowerSeries ℚ) * F) = 342 * coeff m F := by
  have e : (342 : PowerSeries ℚ) = C (342 : ℚ) := (map_ofNat C 342).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn375 : derivative ℚ (375 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 375
@[simp] lemma cc375 : constantCoeff (375 : PowerSeries ℚ) = 375 := by simpa using map_natCast (constantCoeff (R := ℚ)) 375
lemma cm375 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((375 : PowerSeries ℚ) * F) = 375 * coeff m F := by
  have e : (375 : PowerSeries ℚ) = C (375 : ℚ) := (map_ofNat C 375).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn390 : derivative ℚ (390 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 390
@[simp] lemma cc390 : constantCoeff (390 : PowerSeries ℚ) = 390 := by simpa using map_natCast (constantCoeff (R := ℚ)) 390
lemma cm390 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((390 : PowerSeries ℚ) * F) = 390 * coeff m F := by
  have e : (390 : PowerSeries ℚ) = C (390 : ℚ) := (map_ofNat C 390).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn540 : derivative ℚ (540 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 540
@[simp] lemma cc540 : constantCoeff (540 : PowerSeries ℚ) = 540 := by simpa using map_natCast (constantCoeff (R := ℚ)) 540
lemma cm540 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((540 : PowerSeries ℚ) * F) = 540 * coeff m F := by
  have e : (540 : PowerSeries ℚ) = C (540 : ℚ) := (map_ofNat C 540).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn546 : derivative ℚ (546 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 546
@[simp] lemma cc546 : constantCoeff (546 : PowerSeries ℚ) = 546 := by simpa using map_natCast (constantCoeff (R := ℚ)) 546
lemma cm546 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((546 : PowerSeries ℚ) * F) = 546 * coeff m F := by
  have e : (546 : PowerSeries ℚ) = C (546 : ℚ) := (map_ofNat C 546).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn610 : derivative ℚ (610 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 610
@[simp] lemma cc610 : constantCoeff (610 : PowerSeries ℚ) = 610 := by simpa using map_natCast (constantCoeff (R := ℚ)) 610
lemma cm610 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((610 : PowerSeries ℚ) * F) = 610 * coeff m F := by
  have e : (610 : PowerSeries ℚ) = C (610 : ℚ) := (map_ofNat C 610).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn666 : derivative ℚ (666 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 666
@[simp] lemma cc666 : constantCoeff (666 : PowerSeries ℚ) = 666 := by simpa using map_natCast (constantCoeff (R := ℚ)) 666
lemma cm666 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((666 : PowerSeries ℚ) * F) = 666 * coeff m F := by
  have e : (666 : PowerSeries ℚ) = C (666 : ℚ) := (map_ofNat C 666).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn675 : derivative ℚ (675 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 675
@[simp] lemma cc675 : constantCoeff (675 : PowerSeries ℚ) = 675 := by simpa using map_natCast (constantCoeff (R := ℚ)) 675
lemma cm675 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((675 : PowerSeries ℚ) * F) = 675 * coeff m F := by
  have e : (675 : PowerSeries ℚ) = C (675 : ℚ) := (map_ofNat C 675).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn846 : derivative ℚ (846 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 846
@[simp] lemma cc846 : constantCoeff (846 : PowerSeries ℚ) = 846 := by simpa using map_natCast (constantCoeff (R := ℚ)) 846
lemma cm846 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((846 : PowerSeries ℚ) * F) = 846 * coeff m F := by
  have e : (846 : PowerSeries ℚ) = C (846 : ℚ) := (map_ofNat C 846).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn900 : derivative ℚ (900 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 900
@[simp] lemma cc900 : constantCoeff (900 : PowerSeries ℚ) = 900 := by simpa using map_natCast (constantCoeff (R := ℚ)) 900
lemma cm900 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((900 : PowerSeries ℚ) * F) = 900 * coeff m F := by
  have e : (900 : PowerSeries ℚ) = C (900 : ℚ) := (map_ofNat C 900).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn954 : derivative ℚ (954 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 954
@[simp] lemma cc954 : constantCoeff (954 : PowerSeries ℚ) = 954 := by simpa using map_natCast (constantCoeff (R := ℚ)) 954
lemma cm954 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((954 : PowerSeries ℚ) * F) = 954 * coeff m F := by
  have e : (954 : PowerSeries ℚ) = C (954 : ℚ) := (map_ofNat C 954).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1000 : derivative ℚ (1000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1000
@[simp] lemma cc1000 : constantCoeff (1000 : PowerSeries ℚ) = 1000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1000
lemma cm1000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1000 : PowerSeries ℚ) * F) = 1000 * coeff m F := by
  have e : (1000 : PowerSeries ℚ) = C (1000 : ℚ) := (map_ofNat C 1000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1026 : derivative ℚ (1026 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1026
@[simp] lemma cc1026 : constantCoeff (1026 : PowerSeries ℚ) = 1026 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1026
lemma cm1026 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1026 : PowerSeries ℚ) * F) = 1026 * coeff m F := by
  have e : (1026 : PowerSeries ℚ) = C (1026 : ℚ) := (map_ofNat C 1026).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1080 : derivative ℚ (1080 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1080
@[simp] lemma cc1080 : constantCoeff (1080 : PowerSeries ℚ) = 1080 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1080
lemma cm1080 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1080 : PowerSeries ℚ) * F) = 1080 * coeff m F := by
  have e : (1080 : PowerSeries ℚ) = C (1080 : ℚ) := (map_ofNat C 1080).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1092 : derivative ℚ (1092 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1092
@[simp] lemma cc1092 : constantCoeff (1092 : PowerSeries ℚ) = 1092 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1092
lemma cm1092 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1092 : PowerSeries ℚ) * F) = 1092 * coeff m F := by
  have e : (1092 : PowerSeries ℚ) = C (1092 : ℚ) := (map_ofNat C 1092).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1176 : derivative ℚ (1176 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1176
@[simp] lemma cc1176 : constantCoeff (1176 : PowerSeries ℚ) = 1176 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1176
lemma cm1176 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1176 : PowerSeries ℚ) * F) = 1176 * coeff m F := by
  have e : (1176 : PowerSeries ℚ) = C (1176 : ℚ) := (map_ofNat C 1176).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1368 : derivative ℚ (1368 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1368
@[simp] lemma cc1368 : constantCoeff (1368 : PowerSeries ℚ) = 1368 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1368
lemma cm1368 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1368 : PowerSeries ℚ) * F) = 1368 * coeff m F := by
  have e : (1368 : PowerSeries ℚ) = C (1368 : ℚ) := (map_ofNat C 1368).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1500 : derivative ℚ (1500 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1500
@[simp] lemma cc1500 : constantCoeff (1500 : PowerSeries ℚ) = 1500 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1500
lemma cm1500 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1500 : PowerSeries ℚ) * F) = 1500 * coeff m F := by
  have e : (1500 : PowerSeries ℚ) = C (1500 : ℚ) := (map_ofNat C 1500).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1692 : derivative ℚ (1692 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1692
@[simp] lemma cc1692 : constantCoeff (1692 : PowerSeries ℚ) = 1692 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1692
lemma cm1692 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1692 : PowerSeries ℚ) * F) = 1692 * coeff m F := by
  have e : (1692 : PowerSeries ℚ) = C (1692 : ℚ) := (map_ofNat C 1692).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1830 : derivative ℚ (1830 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1830
@[simp] lemma cc1830 : constantCoeff (1830 : PowerSeries ℚ) = 1830 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1830
lemma cm1830 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1830 : PowerSeries ℚ) * F) = 1830 * coeff m F := by
  have e : (1830 : PowerSeries ℚ) = C (1830 : ℚ) := (map_ofNat C 1830).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2664 : derivative ℚ (2664 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2664
@[simp] lemma cc2664 : constantCoeff (2664 : PowerSeries ℚ) = 2664 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2664
lemma cm2664 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2664 : PowerSeries ℚ) * F) = 2664 * coeff m F := by
  have e : (2664 : PowerSeries ℚ) = C (2664 : ℚ) := (map_ofNat C 2664).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2700 : derivative ℚ (2700 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2700
@[simp] lemma cc2700 : constantCoeff (2700 : PowerSeries ℚ) = 2700 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2700
lemma cm2700 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2700 : PowerSeries ℚ) * F) = 2700 * coeff m F := by
  have e : (2700 : PowerSeries ℚ) = C (2700 : ℚ) := (map_ofNat C 2700).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3000 : derivative ℚ (3000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3000
@[simp] lemma cc3000 : constantCoeff (3000 : PowerSeries ℚ) = 3000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3000
lemma cm3000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3000 : PowerSeries ℚ) * F) = 3000 * coeff m F := by
  have e : (3000 : PowerSeries ℚ) = C (3000 : ℚ) := (map_ofNat C 3000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3240 : derivative ℚ (3240 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3240
@[simp] lemma cc3240 : constantCoeff (3240 : PowerSeries ℚ) = 3240 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3240
lemma cm3240 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3240 : PowerSeries ℚ) * F) = 3240 * coeff m F := by
  have e : (3240 : PowerSeries ℚ) = C (3240 : ℚ) := (map_ofNat C 3240).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3660 : derivative ℚ (3660 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3660
@[simp] lemma cc3660 : constantCoeff (3660 : PowerSeries ℚ) = 3660 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3660
lemma cm3660 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3660 : PowerSeries ℚ) * F) = 3660 * coeff m F := by
  have e : (3660 : PowerSeries ℚ) = C (3660 : ℚ) := (map_ofNat C 3660).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4704 : derivative ℚ (4704 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4704
@[simp] lemma cc4704 : constantCoeff (4704 : PowerSeries ℚ) = 4704 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4704
lemma cm4704 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4704 : PowerSeries ℚ) * F) = 4704 * coeff m F := by
  have e : (4704 : PowerSeries ℚ) = C (4704 : ℚ) := (map_ofNat C 4704).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5130 : derivative ℚ (5130 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5130
@[simp] lemma cc5130 : constantCoeff (5130 : PowerSeries ℚ) = 5130 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5130
lemma cm5130 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5130 : PowerSeries ℚ) * F) = 5130 * coeff m F := by
  have e : (5130 : PowerSeries ℚ) = C (5130 : ℚ) := (map_ofNat C 5130).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7992 : derivative ℚ (7992 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7992
@[simp] lemma cc7992 : constantCoeff (7992 : PowerSeries ℚ) = 7992 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7992
lemma cm7992 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7992 : PowerSeries ℚ) * F) = 7992 * coeff m F := by
  have e : (7992 : PowerSeries ℚ) = C (7992 : ℚ) := (map_ofNat C 7992).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16200 : derivative ℚ (16200 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16200
@[simp] lemma cc16200 : constantCoeff (16200 : PowerSeries ℚ) = 16200 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16200
lemma cm16200 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16200 : PowerSeries ℚ) * F) = 16200 * coeff m F := by
  have e : (16200 : PowerSeries ℚ) = C (16200 : ℚ) := (map_ofNat C 16200).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn20520 : derivative ℚ (20520 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20520
@[simp] lemma cc20520 : constantCoeff (20520 : PowerSeries ℚ) = 20520 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20520
lemma cm20520 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20520 : PowerSeries ℚ) * F) = 20520 * coeff m F := by
  have e : (20520 : PowerSeries ℚ) = C (20520 : ℚ) := (map_ofNat C 20520).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn41160 : derivative ℚ (41160 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 41160
@[simp] lemma cc41160 : constantCoeff (41160 : PowerSeries ℚ) = 41160 := by simpa using map_natCast (constantCoeff (R := ℚ)) 41160
lemma cm41160 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((41160 : PowerSeries ℚ) * F) = 41160 * coeff m F := by
  have e : (41160 : PowerSeries ℚ) = C (41160 : ℚ) := (map_ofNat C 41160).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn43512 : derivative ℚ (43512 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 43512
@[simp] lemma cc43512 : constantCoeff (43512 : PowerSeries ℚ) = 43512 := by simpa using map_natCast (constantCoeff (R := ℚ)) 43512
lemma cm43512 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((43512 : PowerSeries ℚ) * F) = 43512 * coeff m F := by
  have e : (43512 : PowerSeries ℚ) = C (43512 : ℚ) := (map_ofNat C 43512).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn122304 : derivative ℚ (122304 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 122304
@[simp] lemma cc122304 : constantCoeff (122304 : PowerSeries ℚ) = 122304 := by simpa using map_natCast (constantCoeff (R := ℚ)) 122304
lemma cm122304 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((122304 : PowerSeries ℚ) * F) = 122304 * coeff m F := by
  have e : (122304 : PowerSeries ℚ) = C (122304 : ℚ) := (map_ofNat C 122304).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn345431 : derivative ℚ (345431 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 345431
@[simp] lemma cc345431 : constantCoeff (345431 : PowerSeries ℚ) = 345431 := by simpa using map_natCast (constantCoeff (R := ℚ)) 345431
lemma cm345431 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((345431 : PowerSeries ℚ) * F) = 345431 * coeff m F := by
  have e : (345431 : PowerSeries ℚ) = C (345431 : ℚ) := (map_ofNat C 345431).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn348959 : derivative ℚ (348959 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 348959
@[simp] lemma cc348959 : constantCoeff (348959 : PowerSeries ℚ) = 348959 := by simpa using map_natCast (constantCoeff (R := ℚ)) 348959
lemma cm348959 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((348959 : PowerSeries ℚ) * F) = 348959 * coeff m F := by
  have e : (348959 : PowerSeries ℚ) = C (348959 : ℚ) := (map_ofNat C 348959).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1177176 : derivative ℚ (1177176 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1177176
@[simp] lemma cc1177176 : constantCoeff (1177176 : PowerSeries ℚ) = 1177176 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1177176
lemma cm1177176 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1177176 : PowerSeries ℚ) * F) = 1177176 * coeff m F := by
  have e : (1177176 : PowerSeries ℚ) = C (1177176 : ℚ) := (map_ofNat C 1177176).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1395836 : derivative ℚ (1395836 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1395836
@[simp] lemma cc1395836 : constantCoeff (1395836 : PowerSeries ℚ) = 1395836 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1395836
lemma cm1395836 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1395836 : PowerSeries ℚ) * F) = 1395836 * coeff m F := by
  have e : (1395836 : PowerSeries ℚ) = C (1395836 : ℚ) := (map_ofNat C 1395836).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2443974 : derivative ℚ (2443974 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2443974
@[simp] lemma cc2443974 : constantCoeff (2443974 : PowerSeries ℚ) = 2443974 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2443974
lemma cm2443974 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2443974 : PowerSeries ℚ) * F) = 2443974 * coeff m F := by
  have e : (2443974 : PowerSeries ℚ) = C (2443974 : ℚ) := (map_ofNat C 2443974).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2790581 : derivative ℚ (2790581 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2790581
@[simp] lemma cc2790581 : constantCoeff (2790581 : PowerSeries ℚ) = 2790581 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2790581
lemma cm2790581 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2790581 : PowerSeries ℚ) * F) = 2790581 * coeff m F := by
  have e : (2790581 : PowerSeries ℚ) = C (2790581 : ℚ) := (map_ofNat C 2790581).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3331731 : derivative ℚ (3331731 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3331731
@[simp] lemma cc3331731 : constantCoeff (3331731 : PowerSeries ℚ) = 3331731 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3331731
lemma cm3331731 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3331731 : PowerSeries ℚ) * F) = 3331731 * coeff m F := by
  have e : (3331731 : PowerSeries ℚ) = C (3331731 : ℚ) := (map_ofNat C 3331731).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3338787 : derivative ℚ (3338787 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3338787
@[simp] lemma cc3338787 : constantCoeff (3338787 : PowerSeries ℚ) = 3338787 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3338787
lemma cm3338787 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3338787 : PowerSeries ℚ) * F) = 3338787 * coeff m F := by
  have e : (3338787 : PowerSeries ℚ) = C (3338787 : ℚ) := (map_ofNat C 3338787).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3366888 : derivative ℚ (3366888 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3366888
@[simp] lemma cc3366888 : constantCoeff (3366888 : PowerSeries ℚ) = 3366888 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3366888
lemma cm3366888 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3366888 : PowerSeries ℚ) * F) = 3366888 * coeff m F := by
  have e : (3366888 : PowerSeries ℚ) = C (3366888 : ℚ) := (map_ofNat C 3366888).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5895885 : derivative ℚ (5895885 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5895885
@[simp] lemma cc5895885 : constantCoeff (5895885 : PowerSeries ℚ) = 5895885 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5895885
lemma cm5895885 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5895885 : PowerSeries ℚ) * F) = 5895885 * coeff m F := by
  have e : (5895885 : PowerSeries ℚ) = C (5895885 : ℚ) := (map_ofNat C 5895885).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6389805 : derivative ℚ (6389805 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6389805
@[simp] lemma cc6389805 : constantCoeff (6389805 : PowerSeries ℚ) = 6389805 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6389805
lemma cm6389805 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6389805 : PowerSeries ℚ) * F) = 6389805 * coeff m F := by
  have e : (6389805 : PowerSeries ℚ) = C (6389805 : ℚ) := (map_ofNat C 6389805).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8972737 : derivative ℚ (8972737 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8972737
@[simp] lemma cc8972737 : constantCoeff (8972737 : PowerSeries ℚ) = 8972737 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8972737
lemma cm8972737 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8972737 : PowerSeries ℚ) * F) = 8972737 * coeff m F := by
  have e : (8972737 : PowerSeries ℚ) = C (8972737 : ℚ) := (map_ofNat C 8972737).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9364345 : derivative ℚ (9364345 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9364345
@[simp] lemma cc9364345 : constantCoeff (9364345 : PowerSeries ℚ) = 9364345 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9364345
lemma cm9364345 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9364345 : PowerSeries ℚ) * F) = 9364345 * coeff m F := by
  have e : (9364345 : PowerSeries ℚ) = C (9364345 : ℚ) := (map_ofNat C 9364345).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9775896 : derivative ℚ (9775896 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9775896
@[simp] lemma cc9775896 : constantCoeff (9775896 : PowerSeries ℚ) = 9775896 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9775896
lemma cm9775896 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9775896 : PowerSeries ℚ) * F) = 9775896 * coeff m F := by
  have e : (9775896 : PowerSeries ℚ) = C (9775896 : ℚ) := (map_ofNat C 9775896).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15693336 : derivative ℚ (15693336 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15693336
@[simp] lemma cc15693336 : constantCoeff (15693336 : PowerSeries ℚ) = 15693336 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15693336
lemma cm15693336 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15693336 : PowerSeries ℚ) * F) = 15693336 * coeff m F := by
  have e : (15693336 : PowerSeries ℚ) = C (15693336 : ℚ) := (map_ofNat C 15693336).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18329805 : derivative ℚ (18329805 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18329805
@[simp] lemma cc18329805 : constantCoeff (18329805 : PowerSeries ℚ) = 18329805 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18329805
lemma cm18329805 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18329805 : PowerSeries ℚ) * F) = 18329805 * coeff m F := by
  have e : (18329805 : PowerSeries ℚ) = C (18329805 : ℚ) := (map_ofNat C 18329805).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn22024545 : derivative ℚ (22024545 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 22024545
@[simp] lemma cc22024545 : constantCoeff (22024545 : PowerSeries ℚ) = 22024545 := by simpa using map_natCast (constantCoeff (R := ℚ)) 22024545
lemma cm22024545 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((22024545 : PowerSeries ℚ) * F) = 22024545 * coeff m F := by
  have e : (22024545 : PowerSeries ℚ) = C (22024545 : ℚ) := (map_ofNat C 22024545).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn29274168 : derivative ℚ (29274168 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 29274168
@[simp] lemma cc29274168 : constantCoeff (29274168 : PowerSeries ℚ) = 29274168 := by simpa using map_natCast (constantCoeff (R := ℚ)) 29274168
lemma cm29274168 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((29274168 : PowerSeries ℚ) * F) = 29274168 * coeff m F := by
  have e : (29274168 : PowerSeries ℚ) = C (29274168 : ℚ) := (map_ofNat C 29274168).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn32032674 : derivative ℚ (32032674 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32032674
@[simp] lemma cc32032674 : constantCoeff (32032674 : PowerSeries ℚ) = 32032674 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32032674
lemma cm32032674 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32032674 : PowerSeries ℚ) * F) = 32032674 * coeff m F := by
  have e : (32032674 : PowerSeries ℚ) = C (32032674 : ℚ) := (map_ofNat C 32032674).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn34536765 : derivative ℚ (34536765 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 34536765
@[simp] lemma cc34536765 : constantCoeff (34536765 : PowerSeries ℚ) = 34536765 := by simpa using map_natCast (constantCoeff (R := ℚ)) 34536765
lemma cm34536765 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((34536765 : PowerSeries ℚ) * F) = 34536765 * coeff m F := by
  have e : (34536765 : PowerSeries ℚ) = C (34536765 : ℚ) := (map_ofNat C 34536765).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn47024868 : derivative ℚ (47024868 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 47024868
@[simp] lemma cc47024868 : constantCoeff (47024868 : PowerSeries ℚ) = 47024868 := by simpa using map_natCast (constantCoeff (R := ℚ)) 47024868
lemma cm47024868 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((47024868 : PowerSeries ℚ) * F) = 47024868 * coeff m F := by
  have e : (47024868 : PowerSeries ℚ) = C (47024868 : ℚ) := (map_ofNat C 47024868).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn50922768 : derivative ℚ (50922768 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 50922768
@[simp] lemma cc50922768 : constantCoeff (50922768 : PowerSeries ℚ) = 50922768 := by simpa using map_natCast (constantCoeff (R := ℚ)) 50922768
lemma cm50922768 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((50922768 : PowerSeries ℚ) * F) = 50922768 * coeff m F := by
  have e : (50922768 : PowerSeries ℚ) = C (50922768 : ℚ) := (map_ofNat C 50922768).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn59204484 : derivative ℚ (59204484 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 59204484
@[simp] lemma cc59204484 : constantCoeff (59204484 : PowerSeries ℚ) = 59204484 := by simpa using map_natCast (constantCoeff (R := ℚ)) 59204484
lemma cm59204484 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((59204484 : PowerSeries ℚ) * F) = 59204484 * coeff m F := by
  have e : (59204484 : PowerSeries ℚ) = C (59204484 : ℚ) := (map_ofNat C 59204484).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn68481945 : derivative ℚ (68481945 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 68481945
@[simp] lemma cc68481945 : constantCoeff (68481945 : PowerSeries ℚ) = 68481945 := by simpa using map_natCast (constantCoeff (R := ℚ)) 68481945
lemma cm68481945 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((68481945 : PowerSeries ℚ) * F) = 68481945 * coeff m F := by
  have e : (68481945 : PowerSeries ℚ) = C (68481945 : ℚ) := (map_ofNat C 68481945).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn72161172 : derivative ℚ (72161172 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 72161172
@[simp] lemma cc72161172 : constantCoeff (72161172 : PowerSeries ℚ) = 72161172 := by simpa using map_natCast (constantCoeff (R := ℚ)) 72161172
lemma cm72161172 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((72161172 : PowerSeries ℚ) * F) = 72161172 * coeff m F := by
  have e : (72161172 : PowerSeries ℚ) = C (72161172 : ℚ) := (map_ofNat C 72161172).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn77742480 : derivative ℚ (77742480 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 77742480
@[simp] lemma cc77742480 : constantCoeff (77742480 : PowerSeries ℚ) = 77742480 := by simpa using map_natCast (constantCoeff (R := ℚ)) 77742480
lemma cm77742480 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((77742480 : PowerSeries ℚ) * F) = 77742480 * coeff m F := by
  have e : (77742480 : PowerSeries ℚ) = C (77742480 : ℚ) := (map_ofNat C 77742480).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80641332 : derivative ℚ (80641332 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80641332
@[simp] lemma cc80641332 : constantCoeff (80641332 : PowerSeries ℚ) = 80641332 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80641332
lemma cm80641332 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80641332 : PowerSeries ℚ) * F) = 80641332 * coeff m F := by
  have e : (80641332 : PowerSeries ℚ) = C (80641332 : ℚ) := (map_ofNat C 80641332).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn103131090 : derivative ℚ (103131090 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 103131090
@[simp] lemma cc103131090 : constantCoeff (103131090 : PowerSeries ℚ) = 103131090 := by simpa using map_natCast (constantCoeff (R := ℚ)) 103131090
lemma cm103131090 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((103131090 : PowerSeries ℚ) * F) = 103131090 * coeff m F := by
  have e : (103131090 : PowerSeries ℚ) = C (103131090 : ℚ) := (map_ofNat C 103131090).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn105199481 : derivative ℚ (105199481 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 105199481
@[simp] lemma cc105199481 : constantCoeff (105199481 : PowerSeries ℚ) = 105199481 := by simpa using map_natCast (constantCoeff (R := ℚ)) 105199481
lemma cm105199481 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((105199481 : PowerSeries ℚ) * F) = 105199481 * coeff m F := by
  have e : (105199481 : PowerSeries ℚ) = C (105199481 : ℚ) := (map_ofNat C 105199481).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn231525000 : derivative ℚ (231525000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 231525000
@[simp] lemma cc231525000 : constantCoeff (231525000 : PowerSeries ℚ) = 231525000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 231525000
lemma cm231525000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((231525000 : PowerSeries ℚ) * F) = 231525000 * coeff m F := by
  have e : (231525000 : PowerSeries ℚ) = C (231525000 : ℚ) := (map_ofNat C 231525000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn245312460 : derivative ℚ (245312460 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 245312460
@[simp] lemma cc245312460 : constantCoeff (245312460 : PowerSeries ℚ) = 245312460 := by simpa using map_natCast (constantCoeff (R := ℚ)) 245312460
lemma cm245312460 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((245312460 : PowerSeries ℚ) * F) = 245312460 * coeff m F := by
  have e : (245312460 : PowerSeries ℚ) = C (245312460 : ℚ) := (map_ofNat C 245312460).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn276420768 : derivative ℚ (276420768 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 276420768
@[simp] lemma cc276420768 : constantCoeff (276420768 : PowerSeries ℚ) = 276420768 := by simpa using map_natCast (constantCoeff (R := ℚ)) 276420768
lemma cm276420768 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((276420768 : PowerSeries ℚ) * F) = 276420768 * coeff m F := by
  have e : (276420768 : PowerSeries ℚ) = C (276420768 : ℚ) := (map_ofNat C 276420768).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn346768296 : derivative ℚ (346768296 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 346768296
@[simp] lemma cc346768296 : constantCoeff (346768296 : PowerSeries ℚ) = 346768296 := by simpa using map_natCast (constantCoeff (R := ℚ)) 346768296
lemma cm346768296 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((346768296 : PowerSeries ℚ) * F) = 346768296 * coeff m F := by
  have e : (346768296 : PowerSeries ℚ) = C (346768296 : ℚ) := (map_ofNat C 346768296).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn360422388 : derivative ℚ (360422388 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 360422388
@[simp] lemma cc360422388 : constantCoeff (360422388 : PowerSeries ℚ) = 360422388 := by simpa using map_natCast (constantCoeff (R := ℚ)) 360422388
lemma cm360422388 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((360422388 : PowerSeries ℚ) * F) = 360422388 * coeff m F := by
  have e : (360422388 : PowerSeries ℚ) = C (360422388 : ℚ) := (map_ofNat C 360422388).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn832351927 : derivative ℚ (832351927 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 832351927
@[simp] lemma cc832351927 : constantCoeff (832351927 : PowerSeries ℚ) = 832351927 := by simpa using map_natCast (constantCoeff (R := ℚ)) 832351927
lemma cm832351927 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((832351927 : PowerSeries ℚ) * F) = 832351927 * coeff m F := by
  have e : (832351927 : PowerSeries ℚ) = C (832351927 : ℚ) := (map_ofNat C 832351927).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1731963408 : derivative ℚ (1731963408 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1731963408
@[simp] lemma cc1731963408 : constantCoeff (1731963408 : PowerSeries ℚ) = 1731963408 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1731963408
lemma cm1731963408 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1731963408 : PowerSeries ℚ) * F) = 1731963408 * coeff m F := by
  have e : (1731963408 : PowerSeries ℚ) = C (1731963408 : ℚ) := (map_ofNat C 1731963408).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1788255000 : derivative ℚ (1788255000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1788255000
@[simp] lemma cc1788255000 : constantCoeff (1788255000 : PowerSeries ℚ) = 1788255000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1788255000
lemma cm1788255000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1788255000 : PowerSeries ℚ) * F) = 1788255000 * coeff m F := by
  have e : (1788255000 : PowerSeries ℚ) = C (1788255000 : ℚ) := (map_ofNat C 1788255000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5211761520 : derivative ℚ (5211761520 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5211761520
@[simp] lemma cc5211761520 : constantCoeff (5211761520 : PowerSeries ℚ) = 5211761520 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5211761520
lemma cm5211761520 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5211761520 : PowerSeries ℚ) * F) = 5211761520 * coeff m F := by
  have e : (5211761520 : PowerSeries ℚ) = C (5211761520 : ℚ) := (map_ofNat C 5211761520).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5951064522 : derivative ℚ (5951064522 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5951064522
@[simp] lemma cc5951064522 : constantCoeff (5951064522 : PowerSeries ℚ) = 5951064522 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5951064522
lemma cm5951064522 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5951064522 : PowerSeries ℚ) * F) = 5951064522 * coeff m F := by
  have e : (5951064522 : PowerSeries ℚ) = C (5951064522 : ℚ) := (map_ofNat C 5951064522).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5951883000 : derivative ℚ (5951883000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5951883000
@[simp] lemma cc5951883000 : constantCoeff (5951883000 : PowerSeries ℚ) = 5951883000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5951883000
lemma cm5951883000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5951883000 : PowerSeries ℚ) * F) = 5951883000 * coeff m F := by
  have e : (5951883000 : PowerSeries ℚ) = C (5951883000 : ℚ) := (map_ofNat C 5951883000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8046738819 : derivative ℚ (8046738819 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8046738819
@[simp] lemma cc8046738819 : constantCoeff (8046738819 : PowerSeries ℚ) = 8046738819 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8046738819
lemma cm8046738819 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8046738819 : PowerSeries ℚ) * F) = 8046738819 * coeff m F := by
  have e : (8046738819 : PowerSeries ℚ) = C (8046738819 : ℚ) := (map_ofNat C 8046738819).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10206407568 : derivative ℚ (10206407568 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10206407568
@[simp] lemma cc10206407568 : constantCoeff (10206407568 : PowerSeries ℚ) = 10206407568 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10206407568
lemma cm10206407568 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10206407568 : PowerSeries ℚ) * F) = 10206407568 * coeff m F := by
  have e : (10206407568 : PowerSeries ℚ) = C (10206407568 : ℚ) := (map_ofNat C 10206407568).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11216070600 : derivative ℚ (11216070600 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11216070600
@[simp] lemma cc11216070600 : constantCoeff (11216070600 : PowerSeries ℚ) = 11216070600 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11216070600
lemma cm11216070600 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11216070600 : PowerSeries ℚ) * F) = 11216070600 * coeff m F := by
  have e : (11216070600 : PowerSeries ℚ) = C (11216070600 : ℚ) := (map_ofNat C 11216070600).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn13232340240 : derivative ℚ (13232340240 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 13232340240
@[simp] lemma cc13232340240 : constantCoeff (13232340240 : PowerSeries ℚ) = 13232340240 := by simpa using map_natCast (constantCoeff (R := ℚ)) 13232340240
lemma cm13232340240 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((13232340240 : PowerSeries ℚ) * F) = 13232340240 * coeff m F := by
  have e : (13232340240 : PowerSeries ℚ) = C (13232340240 : ℚ) := (map_ofNat C 13232340240).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn34785028125 : derivative ℚ (34785028125 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 34785028125
@[simp] lemma cc34785028125 : constantCoeff (34785028125 : PowerSeries ℚ) = 34785028125 := by simpa using map_natCast (constantCoeff (R := ℚ)) 34785028125
lemma cm34785028125 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((34785028125 : PowerSeries ℚ) * F) = 34785028125 * coeff m F := by
  have e : (34785028125 : PowerSeries ℚ) = C (34785028125 : ℚ) := (map_ofNat C 34785028125).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn51157093433 : derivative ℚ (51157093433 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 51157093433
@[simp] lemma cc51157093433 : constantCoeff (51157093433 : PowerSeries ℚ) = 51157093433 := by simpa using map_natCast (constantCoeff (R := ℚ)) 51157093433
lemma cm51157093433 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((51157093433 : PowerSeries ℚ) * F) = 51157093433 * coeff m F := by
  have e : (51157093433 : PowerSeries ℚ) = C (51157093433 : ℚ) := (map_ofNat C 51157093433).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn58084222959 : derivative ℚ (58084222959 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 58084222959
@[simp] lemma cc58084222959 : constantCoeff (58084222959 : PowerSeries ℚ) = 58084222959 := by simpa using map_natCast (constantCoeff (R := ℚ)) 58084222959
lemma cm58084222959 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((58084222959 : PowerSeries ℚ) * F) = 58084222959 * coeff m F := by
  have e : (58084222959 : PowerSeries ℚ) = C (58084222959 : ℚ) := (map_ofNat C 58084222959).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn224984652657 : derivative ℚ (224984652657 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 224984652657
@[simp] lemma cc224984652657 : constantCoeff (224984652657 : PowerSeries ℚ) = 224984652657 := by simpa using map_natCast (constantCoeff (R := ℚ)) 224984652657
lemma cm224984652657 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((224984652657 : PowerSeries ℚ) * F) = 224984652657 * coeff m F := by
  have e : (224984652657 : PowerSeries ℚ) = C (224984652657 : ℚ) := (map_ofNat C 224984652657).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn264765459375 : derivative ℚ (264765459375 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 264765459375
@[simp] lemma cc264765459375 : constantCoeff (264765459375 : PowerSeries ℚ) = 264765459375 := by simpa using map_natCast (constantCoeff (R := ℚ)) 264765459375
lemma cm264765459375 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((264765459375 : PowerSeries ℚ) * F) = 264765459375 * coeff m F := by
  have e : (264765459375 : PowerSeries ℚ) = C (264765459375 : ℚ) := (map_ofNat C 264765459375).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn282973798125 : derivative ℚ (282973798125 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 282973798125
@[simp] lemma cc282973798125 : constantCoeff (282973798125 : PowerSeries ℚ) = 282973798125 := by simpa using map_natCast (constantCoeff (R := ℚ)) 282973798125
lemma cm282973798125 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((282973798125 : PowerSeries ℚ) * F) = 282973798125 * coeff m F := by
  have e : (282973798125 : PowerSeries ℚ) = C (282973798125 : ℚ) := (map_ofNat C 282973798125).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn372573500928 : derivative ℚ (372573500928 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 372573500928
@[simp] lemma cc372573500928 : constantCoeff (372573500928 : PowerSeries ℚ) = 372573500928 := by simpa using map_natCast (constantCoeff (R := ℚ)) 372573500928
lemma cm372573500928 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((372573500928 : PowerSeries ℚ) * F) = 372573500928 * coeff m F := by
  have e : (372573500928 : PowerSeries ℚ) = C (372573500928 : ℚ) := (map_ofNat C 372573500928).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn701240802118 : derivative ℚ (701240802118 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 701240802118
@[simp] lemma cc701240802118 : constantCoeff (701240802118 : PowerSeries ℚ) = 701240802118 := by simpa using map_natCast (constantCoeff (R := ℚ)) 701240802118
lemma cm701240802118 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((701240802118 : PowerSeries ℚ) * F) = 701240802118 * coeff m F := by
  have e : (701240802118 : PowerSeries ℚ) = C (701240802118 : ℚ) := (map_ofNat C 701240802118).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1007353815375 : derivative ℚ (1007353815375 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1007353815375
@[simp] lemma cc1007353815375 : constantCoeff (1007353815375 : PowerSeries ℚ) = 1007353815375 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1007353815375
lemma cm1007353815375 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1007353815375 : PowerSeries ℚ) * F) = 1007353815375 * coeff m F := by
  have e : (1007353815375 : PowerSeries ℚ) = C (1007353815375 : ℚ) := (map_ofNat C 1007353815375).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1561545817566 : derivative ℚ (1561545817566 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1561545817566
@[simp] lemma cc1561545817566 : constantCoeff (1561545817566 : PowerSeries ℚ) = 1561545817566 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1561545817566
lemma cm1561545817566 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1561545817566 : PowerSeries ℚ) * F) = 1561545817566 * coeff m F := by
  have e : (1561545817566 : PowerSeries ℚ) = C (1561545817566 : ℚ) := (map_ofNat C 1561545817566).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1651973973147 : derivative ℚ (1651973973147 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1651973973147
@[simp] lemma cc1651973973147 : constantCoeff (1651973973147 : PowerSeries ℚ) = 1651973973147 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1651973973147
lemma cm1651973973147 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1651973973147 : PowerSeries ℚ) * F) = 1651973973147 * coeff m F := by
  have e : (1651973973147 : PowerSeries ℚ) = C (1651973973147 : ℚ) := (map_ofNat C 1651973973147).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2072826610675 : derivative ℚ (2072826610675 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2072826610675
@[simp] lemma cc2072826610675 : constantCoeff (2072826610675 : PowerSeries ℚ) = 2072826610675 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2072826610675
lemma cm2072826610675 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2072826610675 : PowerSeries ℚ) * F) = 2072826610675 * coeff m F := by
  have e : (2072826610675 : PowerSeries ℚ) = C (2072826610675 : ℚ) := (map_ofNat C 2072826610675).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2149186905000 : derivative ℚ (2149186905000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2149186905000
@[simp] lemma cc2149186905000 : constantCoeff (2149186905000 : PowerSeries ℚ) = 2149186905000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2149186905000
lemma cm2149186905000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2149186905000 : PowerSeries ℚ) * F) = 2149186905000 * coeff m F := by
  have e : (2149186905000 : PowerSeries ℚ) = C (2149186905000 : ℚ) := (map_ofNat C 2149186905000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2474271423086 : derivative ℚ (2474271423086 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2474271423086
@[simp] lemma cc2474271423086 : constantCoeff (2474271423086 : PowerSeries ℚ) = 2474271423086 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2474271423086
lemma cm2474271423086 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2474271423086 : PowerSeries ℚ) * F) = 2474271423086 * coeff m F := by
  have e : (2474271423086 : PowerSeries ℚ) = C (2474271423086 : ℚ) := (map_ofNat C 2474271423086).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2746536499890 : derivative ℚ (2746536499890 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2746536499890
@[simp] lemma cc2746536499890 : constantCoeff (2746536499890 : PowerSeries ℚ) = 2746536499890 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2746536499890
lemma cm2746536499890 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2746536499890 : PowerSeries ℚ) * F) = 2746536499890 * coeff m F := by
  have e : (2746536499890 : PowerSeries ℚ) = C (2746536499890 : ℚ) := (map_ofNat C 2746536499890).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5186860340268 : derivative ℚ (5186860340268 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5186860340268
@[simp] lemma cc5186860340268 : constantCoeff (5186860340268 : PowerSeries ℚ) = 5186860340268 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5186860340268
lemma cm5186860340268 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5186860340268 : PowerSeries ℚ) * F) = 5186860340268 * coeff m F := by
  have e : (5186860340268 : PowerSeries ℚ) = C (5186860340268 : ℚ) := (map_ofNat C 5186860340268).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7630750177875 : derivative ℚ (7630750177875 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7630750177875
@[simp] lemma cc7630750177875 : constantCoeff (7630750177875 : PowerSeries ℚ) = 7630750177875 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7630750177875
lemma cm7630750177875 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7630750177875 : PowerSeries ℚ) * F) = 7630750177875 * coeff m F := by
  have e : (7630750177875 : PowerSeries ℚ) = C (7630750177875 : ℚ) := (map_ofNat C 7630750177875).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11625158452446 : derivative ℚ (11625158452446 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11625158452446
@[simp] lemma cc11625158452446 : constantCoeff (11625158452446 : PowerSeries ℚ) = 11625158452446 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11625158452446
lemma cm11625158452446 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11625158452446 : PowerSeries ℚ) * F) = 11625158452446 * coeff m F := by
  have e : (11625158452446 : PowerSeries ℚ) = C (11625158452446 : ℚ) := (map_ofNat C 11625158452446).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15651500842650 : derivative ℚ (15651500842650 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15651500842650
@[simp] lemma cc15651500842650 : constantCoeff (15651500842650 : PowerSeries ℚ) = 15651500842650 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15651500842650
lemma cm15651500842650 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15651500842650 : PowerSeries ℚ) * F) = 15651500842650 * coeff m F := by
  have e : (15651500842650 : PowerSeries ℚ) = C (15651500842650 : ℚ) := (map_ofNat C 15651500842650).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18522906918576 : derivative ℚ (18522906918576 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18522906918576
@[simp] lemma cc18522906918576 : constantCoeff (18522906918576 : PowerSeries ℚ) = 18522906918576 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18522906918576
lemma cm18522906918576 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18522906918576 : PowerSeries ℚ) * F) = 18522906918576 * coeff m F := by
  have e : (18522906918576 : PowerSeries ℚ) = C (18522906918576 : ℚ) := (map_ofNat C 18522906918576).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn20657896639650 : derivative ℚ (20657896639650 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20657896639650
@[simp] lemma cc20657896639650 : constantCoeff (20657896639650 : PowerSeries ℚ) = 20657896639650 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20657896639650
lemma cm20657896639650 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20657896639650 : PowerSeries ℚ) * F) = 20657896639650 * coeff m F := by
  have e : (20657896639650 : PowerSeries ℚ) = C (20657896639650 : ℚ) := (map_ofNat C 20657896639650).symm
  rw [e, coeff_C_mul]

lemma S_sq : S * S = R := by
  have := bs_sq (R - 1) (by simp [R])
  unfold S; rw [this]; ring

noncomputable def DD : PowerSeries ℚ := 2 - 12 * X + 10 * X ^ 2
noncomputable def NN : PowerSeries ℚ := -2 + 27 * X - 136 * X ^ 2 + 318 * X ^ 3 - 342 * X ^ 4 + 135 * X ^ 5 + (2 - 21 * X + 77 * X ^ 2 - 111 * X ^ 3 + 45 * X ^ 4) * S
noncomputable def AA : PowerSeries ℚ := NN * DD⁻¹

lemma hA : AA * DD = NN := by
  unfold AA
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [DD]), mul_one]

lemma hdD : derivative ℚ DD = 20*X - 12 := by
  simp [DD] <;> ring
lemma hdR : derivative ℚ R = 10*X - 6 := by
  simp [R] <;> ring
lemma hdN : derivative ℚ NN = 675*X^4 - 1368*X^3 + 954*X^2 - 272*X + 27 + (180*X^3 - 333*X^2 + 154*X - 21) * S + (45*X^4 - 111*X^3 + 77*X^2 - 21*X + 2) * derivative ℚ S := by
  simp [NN] <;> ring

lemma ode1 : ((-2) * X ^ 0 + (27) * X ^ 1 + (-132) * X ^ 2 + (282) * X ^ 3 + (-250) * X ^ 4 + (75) * X ^ 5 : PowerSeries ℚ) * derivative ℚ AA + ((-15) * X ^ 0 + (162) * X ^ 1 + (-540) * X ^ 2 + (610) * X ^ 3 + (-225) * X ^ 4 : PowerSeries ℚ) * AA = ((-18) * X ^ 2 + (182) * X ^ 3 + (-666) * X ^ 4 + (1026) * X ^ 5 + (-540) * X ^ 6 : PowerSeries ℚ) := by
  have r1 := hA
  have r2 : derivative ℚ AA * DD + AA * derivative ℚ DD = derivative ℚ NN := by
    have := congrArg (derivative ℚ) hA
    rw [Derivation.leibniz] at this
    simp only [smul_eq_mul] at this
    rw [← this]; ring
  have r4 := sqrt_ode S R S_sq
  have hK : (2 * R * DD ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp [R, DD] at this
  apply mul_left_cancel₀ hK
  rw [hdD, hdN] at r2
  rw [hdR] at r4
  unfold NN at r1
  unfold DD at r1 r2
  unfold R at r4
  unfold DD R
  linear_combination (-37500*X^8 + 192000*X^7 - 402000*X^6 + 444560*X^5 - 280728*X^4 + 102944*X^3 - 21552*X^2 + 2384*X - 108) * r1 + (7500*X^9 - 43000*X^8 + 102000*X^7 - 130480*X^6 + 98568*X^5 - 45504*X^4 + 12912*X^3 - 2192*X^2 + 204*X - 8) * r2 + (33750*X^11 - 236250*X^10 + 703800*X^9 - 1174400*X^8 + 1219044*X^7 - 828636*X^6 + 378408*X^5 - 116840*X^4 + 24054*X^3 - 3162*X^2 + 240*X - 8) * r4

lemma hdV : derivative ℚ ((-2) * X ^ 0 + (27) * X ^ 1 + (-132) * X ^ 2 + (282) * X ^ 3 + (-250) * X ^ 4 + (75) * X ^ 5 : PowerSeries ℚ) = ((27) * X ^ 0 + (-264) * X ^ 1 + (846) * X ^ 2 + (-1000) * X ^ 3 + (375) * X ^ 4 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdU : derivative ℚ ((-15) * X ^ 0 + (162) * X ^ 1 + (-540) * X ^ 2 + (610) * X ^ 3 + (-225) * X ^ 4 : PowerSeries ℚ) = ((162) * X ^ 0 + (-1080) * X ^ 1 + (1830) * X ^ 2 + (-900) * X ^ 3 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdW : derivative ℚ ((-18) * X ^ 2 + (182) * X ^ 3 + (-666) * X ^ 4 + (1026) * X ^ 5 + (-540) * X ^ 6 : PowerSeries ℚ) = ((-36) * X ^ 1 + (546) * X ^ 2 + (-2664) * X ^ 3 + (5130) * X ^ 4 + (-3240) * X ^ 5 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdV1 : derivative ℚ ((27) * X ^ 0 + (-264) * X ^ 1 + (846) * X ^ 2 + (-1000) * X ^ 3 + (375) * X ^ 4 : PowerSeries ℚ) = ((-264) * X ^ 0 + (1692) * X ^ 1 + (-3000) * X ^ 2 + (1500) * X ^ 3 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdU1 : derivative ℚ ((162) * X ^ 0 + (-1080) * X ^ 1 + (1830) * X ^ 2 + (-900) * X ^ 3 : PowerSeries ℚ) = ((-1080) * X ^ 0 + (3660) * X ^ 1 + (-2700) * X ^ 2 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdW1 : derivative ℚ ((-36) * X ^ 1 + (546) * X ^ 2 + (-2664) * X ^ 3 + (5130) * X ^ 4 + (-3240) * X ^ 5 : PowerSeries ℚ) = ((-36) * X ^ 0 + (1092) * X ^ 1 + (-7992) * X ^ 2 + (20520) * X ^ 3 + (-16200) * X ^ 4 : PowerSeries ℚ) := by
  simp <;> ring

lemma dmul (F G : PowerSeries ℚ) : derivative ℚ (F * G) = F * derivative ℚ G + G * derivative ℚ F := by
  rw [Derivation.leibniz]; simp only [smul_eq_mul]

lemma ode2 : ((27) * X ^ 0 + (-264) * X ^ 1 + (846) * X ^ 2 + (-1000) * X ^ 3 + (375) * X ^ 4 : PowerSeries ℚ) * derivative ℚ AA + ((-2) * X ^ 0 + (27) * X ^ 1 + (-132) * X ^ 2 + (282) * X ^ 3 + (-250) * X ^ 4 + (75) * X ^ 5 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((162) * X ^ 0 + (-1080) * X ^ 1 + (1830) * X ^ 2 + (-900) * X ^ 3 : PowerSeries ℚ) * AA + ((-15) * X ^ 0 + (162) * X ^ 1 + (-540) * X ^ 2 + (610) * X ^ 3 + (-225) * X ^ 4 : PowerSeries ℚ) * derivative ℚ AA = ((-36) * X ^ 1 + (546) * X ^ 2 + (-2664) * X ^ 3 + (5130) * X ^ 4 + (-3240) * X ^ 5 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) ode1
  rw [map_add, dmul, dmul, hdV, hdU, hdW] at h
  linear_combination h

lemma ode3' : ((-264) * X ^ 0 + (1692) * X ^ 1 + (-3000) * X ^ 2 + (1500) * X ^ 3 : PowerSeries ℚ) * derivative ℚ AA + ((27) * X ^ 0 + (-264) * X ^ 1 + (846) * X ^ 2 + (-1000) * X ^ 3 + (375) * X ^ 4 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + (((27) * X ^ 0 + (-264) * X ^ 1 + (846) * X ^ 2 + (-1000) * X ^ 3 + (375) * X ^ 4 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((-2) * X ^ 0 + (27) * X ^ 1 + (-132) * X ^ 2 + (282) * X ^ 3 + (-250) * X ^ 4 + (75) * X ^ 5 : PowerSeries ℚ) * derivative ℚ (derivative ℚ (derivative ℚ AA))) + (((-1080) * X ^ 0 + (3660) * X ^ 1 + (-2700) * X ^ 2 : PowerSeries ℚ) * AA + ((162) * X ^ 0 + (-1080) * X ^ 1 + (1830) * X ^ 2 + (-900) * X ^ 3 : PowerSeries ℚ) * derivative ℚ AA) + (((162) * X ^ 0 + (-1080) * X ^ 1 + (1830) * X ^ 2 + (-900) * X ^ 3 : PowerSeries ℚ) * derivative ℚ AA + ((-15) * X ^ 0 + (162) * X ^ 1 + (-540) * X ^ 2 + (610) * X ^ 3 + (-225) * X ^ 4 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA)) = ((-36) * X ^ 0 + (1092) * X ^ 1 + (-7992) * X ^ 2 + (20520) * X ^ 3 + (-16200) * X ^ 4 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) ode2
  rw [map_add, map_add, map_add, dmul, dmul, dmul, dmul, hdV1, hdV, hdU1, hdU, hdW1] at h
  linear_combination h

lemma ode3 : ((18329805) * X ^ 1 + (-103131090) * X ^ 2 + (68481945) * X ^ 3 : PowerSeries ℚ) * AA + ((2443974) * X ^ 1 + (-22024545) * X ^ 2 + (59204484) * X ^ 3 + (-34536765) * X ^ 4 : PowerSeries ℚ) * derivative ℚ AA + ((-348959) * X ^ 2 + (3331731) * X ^ 3 + (-8972737) * X ^ 4 + (5895885) * X ^ 5 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((-1176) * X ^ 3 + (-1176) * X ^ 4 + (43512) * X ^ 5 + (-41160) * X ^ 6 : PowerSeries ℚ) * derivative ℚ (derivative ℚ (derivative ℚ AA)) = ((15693336) * X ^ 3 + (-72161172) * X ^ 4 + (80641332) * X ^ 5 : PowerSeries ℚ) := by
  have e1 := ode1
  have e2 := ode2
  have e3 := ode3'
  have hK : (((-2) * X ^ 0 + (27) * X ^ 1 + (-132) * X ^ 2 + (282) * X ^ 3 + (-250) * X ^ 4 + (75) * X ^ 5 : PowerSeries ℚ) ^ 3 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  apply mul_left_cancel₀ hK
  linear_combination (((-4704) * X ^ 3 + (122304) * X ^ 4 + (-1177176) * X ^ 5 + (3366888) * X ^ 6 + (29274168) * X ^ 7 + (-346768296) * X ^ 8 + (1731963408) * X ^ 9 + (-5211761520) * X ^ 10 + (10206407568) * X ^ 11 + (-13232340240) * X ^ 12 + (11216070600) * X ^ 13 + (-5951883000) * X ^ 14 + (1788255000) * X ^ 15 + (-231525000) * X ^ 16 : PowerSeries ℚ)) * e3 + (((-1395836) * X ^ 2 + (50922768) * X ^ 3 + (-832351927) * X ^ 4 + (8046738819) * X ^ 5 + (-51157093433) * X ^ 6 + (224984652657) * X ^ 7 + (-701240802118) * X ^ 8 + (1561545817566) * X ^ 9 + (-2474271423086) * X ^ 10 + (2746536499890) * X ^ 11 + (-2072826610675) * X ^ 12 + (1007353815375) * X ^ 13 + (-282973798125) * X ^ 14 + (34785028125) * X ^ 15 : PowerSeries ℚ)) * e2 + (((9775896) * X ^ 1 + (-360422388) * X ^ 2 + (5951064522) * X ^ 3 + (-58084222959) * X ^ 4 + (372573500928) * X ^ 5 + (-1651973973147) * X ^ 6 + (5186860340268) * X ^ 7 + (-11625158452446) * X ^ 8 + (18522906918576) * X ^ 9 + (-20657896639650) * X ^ 10 + (15651500842650) * X ^ 11 + (-7630750177875) * X ^ 12 + (2149186905000) * X ^ 13 + (-264765459375) * X ^ 14 : PowerSeries ℚ)) * e1

lemma ha (n : ℕ) : a n = coeff (n + 2) AA := rfl

lemma rec_a (k : ℕ) : (-1176*((k + 4 : ℕ) : ℚ)^3 - 352487*((k + 4 : ℕ) : ℚ)^2 + 1394745*((k + 4 : ℕ) : ℚ) + 4190030) * a (k + 4) + (-1176*((k + 4 : ℕ) : ℚ)^3 + 3331731*((k + 4 : ℕ) : ℚ)^2 - 18691638*((k + 4 : ℕ) : ℚ) - 3694740) * a (k + 3) + (43512*((k + 4 : ℕ) : ℚ)^3 - 9103273*((k + 4 : ℕ) : ℚ)^2 + 68264245*((k + 4 : ℕ) : ℚ) - 103131090) * a (k + 2) + (-41160*((k + 4 : ℕ) : ℚ)^3 + 6142845*((k + 4 : ℕ) : ℚ)^2 - 52677180*((k + 4 : ℕ) : ℚ) + 115057440) * a (k + 1) = 0 := by
  have h := congrArg (coeff (k + 6)) ode3
  simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm13, cm14, cm15, cm16, cm18, cm20, cm21, cm27, cm36, cm45, cm75, cm77, cm102, cm111, cm132, cm135, cm136, cm150, cm154, cm162, cm180, cm182, cm225, cm250, cm264, cm272, cm282, cm306, cm318, cm333, cm342, cm375, cm390, cm540, cm546, cm610, cm666, cm675, cm846, cm900, cm954, cm1000, cm1026, cm1080, cm1092, cm1176, cm1368, cm1500, cm1692, cm1830, cm2664, cm2700, cm3000, cm3240, cm3660, cm4704, cm5130, cm7992, cm16200, cm20520, cm41160, cm43512, cm122304, cm345431, cm348959, cm1177176, cm1395836, cm2443974, cm2790581, cm3331731, cm3338787, cm3366888, cm5895885, cm6389805, cm8972737, cm9364345, cm9775896, cm15693336, cm18329805, cm22024545, cm29274168, cm32032674, cm34536765, cm47024868, cm50922768, cm59204484, cm68481945, cm72161172, cm77742480, cm80641332, cm103131090, cm105199481, cm231525000, cm245312460, cm276420768, cm346768296, cm360422388, cm832351927, cm1731963408, cm1788255000, cm5211761520, cm5951064522, cm5951883000, cm8046738819, cm10206407568, cm11216070600, cm13232340240, cm34785028125, cm51157093433, cm58084222959, cm224984652657, cm264765459375, cm282973798125, cm372573500928, cm701240802118, cm1007353815375, cm1561545817566, cm1651973973147, cm2072826610675, cm2149186905000, cm2474271423086, cm2746536499890, cm5186860340268, cm7630750177875, cm11625158452446, cm15651500842650, cm18522906918576, cm20657896639650, coeff_X_pow_mul', coeff_derivative] at h
  simp [PowerSeries.coeff_X] at h
  simp only [ha]
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at h ⊢
  push_cast at h ⊢
  try simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
  linear_combination h

end OMA.S_oeis_a126323

theorem OMA.solution : type_of% @OMA.S_oeis_a126323.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega]
  have h := OMA.S_oeis_a126323.rec_a k
  push_cast at h ⊢
  linear_combination h
