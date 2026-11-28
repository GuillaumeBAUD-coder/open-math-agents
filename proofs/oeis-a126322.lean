import OMAStatements.S_oeis_a126322
import Mathlib

namespace OMA.S_oeis_a126322

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
@[simp] lemma dn17 : derivative ℚ (17 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17
@[simp] lemma cc17 : constantCoeff (17 : PowerSeries ℚ) = 17 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17
lemma cm17 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17 : PowerSeries ℚ) * F) = 17 * coeff m F := by
  have e : (17 : PowerSeries ℚ) = C (17 : ℚ) := (map_ofNat C 17).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18 : derivative ℚ (18 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18
@[simp] lemma cc18 : constantCoeff (18 : PowerSeries ℚ) = 18 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18
lemma cm18 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18 : PowerSeries ℚ) * F) = 18 * coeff m F := by
  have e : (18 : PowerSeries ℚ) = C (18 : ℚ) := (map_ofNat C 18).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn19 : derivative ℚ (19 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 19
@[simp] lemma cc19 : constantCoeff (19 : PowerSeries ℚ) = 19 := by simpa using map_natCast (constantCoeff (R := ℚ)) 19
lemma cm19 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((19 : PowerSeries ℚ) * F) = 19 * coeff m F := by
  have e : (19 : PowerSeries ℚ) = C (19 : ℚ) := (map_ofNat C 19).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn24 : derivative ℚ (24 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24
@[simp] lemma cc24 : constantCoeff (24 : PowerSeries ℚ) = 24 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24
lemma cm24 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24 : PowerSeries ℚ) * F) = 24 * coeff m F := by
  have e : (24 : PowerSeries ℚ) = C (24 : ℚ) := (map_ofNat C 24).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn25 : derivative ℚ (25 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 25
@[simp] lemma cc25 : constantCoeff (25 : PowerSeries ℚ) = 25 := by simpa using map_natCast (constantCoeff (R := ℚ)) 25
lemma cm25 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((25 : PowerSeries ℚ) * F) = 25 * coeff m F := by
  have e : (25 : PowerSeries ℚ) = C (25 : ℚ) := (map_ofNat C 25).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn27 : derivative ℚ (27 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 27
@[simp] lemma cc27 : constantCoeff (27 : PowerSeries ℚ) = 27 := by simpa using map_natCast (constantCoeff (R := ℚ)) 27
lemma cm27 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((27 : PowerSeries ℚ) * F) = 27 * coeff m F := by
  have e : (27 : PowerSeries ℚ) = C (27 : ℚ) := (map_ofNat C 27).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn30 : derivative ℚ (30 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 30
@[simp] lemma cc30 : constantCoeff (30 : PowerSeries ℚ) = 30 := by simpa using map_natCast (constantCoeff (R := ℚ)) 30
lemma cm30 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((30 : PowerSeries ℚ) * F) = 30 * coeff m F := by
  have e : (30 : PowerSeries ℚ) = C (30 : ℚ) := (map_ofNat C 30).symm
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
@[simp] lemma dn54 : derivative ℚ (54 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 54
@[simp] lemma cc54 : constantCoeff (54 : PowerSeries ℚ) = 54 := by simpa using map_natCast (constantCoeff (R := ℚ)) 54
lemma cm54 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((54 : PowerSeries ℚ) * F) = 54 * coeff m F := by
  have e : (54 : PowerSeries ℚ) = C (54 : ℚ) := (map_ofNat C 54).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn72 : derivative ℚ (72 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 72
@[simp] lemma cc72 : constantCoeff (72 : PowerSeries ℚ) = 72 := by simpa using map_natCast (constantCoeff (R := ℚ)) 72
lemma cm72 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((72 : PowerSeries ℚ) * F) = 72 * coeff m F := by
  have e : (72 : PowerSeries ℚ) = C (72 : ℚ) := (map_ofNat C 72).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn81 : derivative ℚ (81 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 81
@[simp] lemma cc81 : constantCoeff (81 : PowerSeries ℚ) = 81 := by simpa using map_natCast (constantCoeff (R := ℚ)) 81
lemma cm81 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((81 : PowerSeries ℚ) * F) = 81 * coeff m F := by
  have e : (81 : PowerSeries ℚ) = C (81 : ℚ) := (map_ofNat C 81).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn105 : derivative ℚ (105 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 105
@[simp] lemma cc105 : constantCoeff (105 : PowerSeries ℚ) = 105 := by simpa using map_natCast (constantCoeff (R := ℚ)) 105
lemma cm105 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((105 : PowerSeries ℚ) * F) = 105 * coeff m F := by
  have e : (105 : PowerSeries ℚ) = C (105 : ℚ) := (map_ofNat C 105).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn108 : derivative ℚ (108 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 108
@[simp] lemma cc108 : constantCoeff (108 : PowerSeries ℚ) = 108 := by simpa using map_natCast (constantCoeff (R := ℚ)) 108
lemma cm108 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((108 : PowerSeries ℚ) * F) = 108 * coeff m F := by
  have e : (108 : PowerSeries ℚ) = C (108 : ℚ) := (map_ofNat C 108).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn120 : derivative ℚ (120 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 120
@[simp] lemma cc120 : constantCoeff (120 : PowerSeries ℚ) = 120 := by simpa using map_natCast (constantCoeff (R := ℚ)) 120
lemma cm120 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((120 : PowerSeries ℚ) * F) = 120 * coeff m F := by
  have e : (120 : PowerSeries ℚ) = C (120 : ℚ) := (map_ofNat C 120).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn144 : derivative ℚ (144 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 144
@[simp] lemma cc144 : constantCoeff (144 : PowerSeries ℚ) = 144 := by simpa using map_natCast (constantCoeff (R := ℚ)) 144
lemma cm144 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((144 : PowerSeries ℚ) * F) = 144 * coeff m F := by
  have e : (144 : PowerSeries ℚ) = C (144 : ℚ) := (map_ofNat C 144).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn150 : derivative ℚ (150 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 150
@[simp] lemma cc150 : constantCoeff (150 : PowerSeries ℚ) = 150 := by simpa using map_natCast (constantCoeff (R := ℚ)) 150
lemma cm150 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((150 : PowerSeries ℚ) * F) = 150 * coeff m F := by
  have e : (150 : PowerSeries ℚ) = C (150 : ℚ) := (map_ofNat C 150).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn171 : derivative ℚ (171 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 171
@[simp] lemma cc171 : constantCoeff (171 : PowerSeries ℚ) = 171 := by simpa using map_natCast (constantCoeff (R := ℚ)) 171
lemma cm171 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((171 : PowerSeries ℚ) * F) = 171 * coeff m F := by
  have e : (171 : PowerSeries ℚ) = C (171 : ℚ) := (map_ofNat C 171).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn180 : derivative ℚ (180 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 180
@[simp] lemma cc180 : constantCoeff (180 : PowerSeries ℚ) = 180 := by simpa using map_natCast (constantCoeff (R := ℚ)) 180
lemma cm180 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((180 : PowerSeries ℚ) * F) = 180 * coeff m F := by
  have e : (180 : PowerSeries ℚ) = C (180 : ℚ) := (map_ofNat C 180).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn189 : derivative ℚ (189 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 189
@[simp] lemma cc189 : constantCoeff (189 : PowerSeries ℚ) = 189 := by simpa using map_natCast (constantCoeff (R := ℚ)) 189
lemma cm189 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((189 : PowerSeries ℚ) * F) = 189 * coeff m F := by
  have e : (189 : PowerSeries ℚ) = C (189 : ℚ) := (map_ofNat C 189).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn216 : derivative ℚ (216 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 216
@[simp] lemma cc216 : constantCoeff (216 : PowerSeries ℚ) = 216 := by simpa using map_natCast (constantCoeff (R := ℚ)) 216
lemma cm216 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((216 : PowerSeries ℚ) * F) = 216 * coeff m F := by
  have e : (216 : PowerSeries ℚ) = C (216 : ℚ) := (map_ofNat C 216).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn225 : derivative ℚ (225 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 225
@[simp] lemma cc225 : constantCoeff (225 : PowerSeries ℚ) = 225 := by simpa using map_natCast (constantCoeff (R := ℚ)) 225
lemma cm225 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((225 : PowerSeries ℚ) * F) = 225 * coeff m F := by
  have e : (225 : PowerSeries ℚ) = C (225 : ℚ) := (map_ofNat C 225).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn243 : derivative ℚ (243 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 243
@[simp] lemma cc243 : constantCoeff (243 : PowerSeries ℚ) = 243 := by simpa using map_natCast (constantCoeff (R := ℚ)) 243
lemma cm243 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((243 : PowerSeries ℚ) * F) = 243 * coeff m F := by
  have e : (243 : PowerSeries ℚ) = C (243 : ℚ) := (map_ofNat C 243).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn324 : derivative ℚ (324 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 324
@[simp] lemma cc324 : constantCoeff (324 : PowerSeries ℚ) = 324 := by simpa using map_natCast (constantCoeff (R := ℚ)) 324
lemma cm324 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((324 : PowerSeries ℚ) * F) = 324 * coeff m F := by
  have e : (324 : PowerSeries ℚ) = C (324 : ℚ) := (map_ofNat C 324).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn360 : derivative ℚ (360 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 360
@[simp] lemma cc360 : constantCoeff (360 : PowerSeries ℚ) = 360 := by simpa using map_natCast (constantCoeff (R := ℚ)) 360
lemma cm360 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((360 : PowerSeries ℚ) * F) = 360 * coeff m F := by
  have e : (360 : PowerSeries ℚ) = C (360 : ℚ) := (map_ofNat C 360).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn378 : derivative ℚ (378 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 378
@[simp] lemma cc378 : constantCoeff (378 : PowerSeries ℚ) = 378 := by simpa using map_natCast (constantCoeff (R := ℚ)) 378
lemma cm378 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((378 : PowerSeries ℚ) * F) = 378 * coeff m F := by
  have e : (378 : PowerSeries ℚ) = C (378 : ℚ) := (map_ofNat C 378).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn405 : derivative ℚ (405 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 405
@[simp] lemma cc405 : constantCoeff (405 : PowerSeries ℚ) = 405 := by simpa using map_natCast (constantCoeff (R := ℚ)) 405
lemma cm405 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((405 : PowerSeries ℚ) * F) = 405 * coeff m F := by
  have e : (405 : PowerSeries ℚ) = C (405 : ℚ) := (map_ofNat C 405).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn486 : derivative ℚ (486 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 486
@[simp] lemma cc486 : constantCoeff (486 : PowerSeries ℚ) = 486 := by simpa using map_natCast (constantCoeff (R := ℚ)) 486
lemma cm486 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((486 : PowerSeries ℚ) * F) = 486 * coeff m F := by
  have e : (486 : PowerSeries ℚ) = C (486 : ℚ) := (map_ofNat C 486).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn513 : derivative ℚ (513 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 513
@[simp] lemma cc513 : constantCoeff (513 : PowerSeries ℚ) = 513 := by simpa using map_natCast (constantCoeff (R := ℚ)) 513
lemma cm513 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((513 : PowerSeries ℚ) * F) = 513 * coeff m F := by
  have e : (513 : PowerSeries ℚ) = C (513 : ℚ) := (map_ofNat C 513).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn540 : derivative ℚ (540 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 540
@[simp] lemma cc540 : constantCoeff (540 : PowerSeries ℚ) = 540 := by simpa using map_natCast (constantCoeff (R := ℚ)) 540
lemma cm540 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((540 : PowerSeries ℚ) * F) = 540 * coeff m F := by
  have e : (540 : PowerSeries ℚ) = C (540 : ℚ) := (map_ofNat C 540).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn600 : derivative ℚ (600 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 600
@[simp] lemma cc600 : constantCoeff (600 : PowerSeries ℚ) = 600 := by simpa using map_natCast (constantCoeff (R := ℚ)) 600
lemma cm600 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((600 : PowerSeries ℚ) * F) = 600 * coeff m F := by
  have e : (600 : PowerSeries ℚ) = C (600 : ℚ) := (map_ofNat C 600).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn617 : derivative ℚ (617 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 617
@[simp] lemma cc617 : constantCoeff (617 : PowerSeries ℚ) = 617 := by simpa using map_natCast (constantCoeff (R := ℚ)) 617
lemma cm617 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((617 : PowerSeries ℚ) * F) = 617 * coeff m F := by
  have e : (617 : PowerSeries ℚ) = C (617 : ℚ) := (map_ofNat C 617).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn648 : derivative ℚ (648 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 648
@[simp] lemma cc648 : constantCoeff (648 : PowerSeries ℚ) = 648 := by simpa using map_natCast (constantCoeff (R := ℚ)) 648
lemma cm648 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((648 : PowerSeries ℚ) * F) = 648 * coeff m F := by
  have e : (648 : PowerSeries ℚ) = C (648 : ℚ) := (map_ofNat C 648).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn672 : derivative ℚ (672 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 672
@[simp] lemma cc672 : constantCoeff (672 : PowerSeries ℚ) = 672 := by simpa using map_natCast (constantCoeff (R := ℚ)) 672
lemma cm672 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((672 : PowerSeries ℚ) * F) = 672 * coeff m F := by
  have e : (672 : PowerSeries ℚ) = C (672 : ℚ) := (map_ofNat C 672).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn720 : derivative ℚ (720 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 720
@[simp] lemma cc720 : constantCoeff (720 : PowerSeries ℚ) = 720 := by simpa using map_natCast (constantCoeff (R := ℚ)) 720
lemma cm720 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((720 : PowerSeries ℚ) * F) = 720 * coeff m F := by
  have e : (720 : PowerSeries ℚ) = C (720 : ℚ) := (map_ofNat C 720).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn828 : derivative ℚ (828 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 828
@[simp] lemma cc828 : constantCoeff (828 : PowerSeries ℚ) = 828 := by simpa using map_natCast (constantCoeff (R := ℚ)) 828
lemma cm828 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((828 : PowerSeries ℚ) * F) = 828 * coeff m F := by
  have e : (828 : PowerSeries ℚ) = C (828 : ℚ) := (map_ofNat C 828).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn855 : derivative ℚ (855 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 855
@[simp] lemma cc855 : constantCoeff (855 : PowerSeries ℚ) = 855 := by simpa using map_natCast (constantCoeff (R := ℚ)) 855
lemma cm855 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((855 : PowerSeries ℚ) * F) = 855 * coeff m F := by
  have e : (855 : PowerSeries ℚ) = C (855 : ℚ) := (map_ofNat C 855).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn900 : derivative ℚ (900 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 900
@[simp] lemma cc900 : constantCoeff (900 : PowerSeries ℚ) = 900 := by simpa using map_natCast (constantCoeff (R := ℚ)) 900
lemma cm900 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((900 : PowerSeries ℚ) * F) = 900 * coeff m F := by
  have e : (900 : PowerSeries ℚ) = C (900 : ℚ) := (map_ofNat C 900).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1026 : derivative ℚ (1026 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1026
@[simp] lemma cc1026 : constantCoeff (1026 : PowerSeries ℚ) = 1026 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1026
lemma cm1026 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1026 : PowerSeries ℚ) * F) = 1026 * coeff m F := by
  have e : (1026 : PowerSeries ℚ) = C (1026 : ℚ) := (map_ofNat C 1026).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1152 : derivative ℚ (1152 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1152
@[simp] lemma cc1152 : constantCoeff (1152 : PowerSeries ℚ) = 1152 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1152
lemma cm1152 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1152 : PowerSeries ℚ) * F) = 1152 * coeff m F := by
  have e : (1152 : PowerSeries ℚ) = C (1152 : ℚ) := (map_ofNat C 1152).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1296 : derivative ℚ (1296 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1296
@[simp] lemma cc1296 : constantCoeff (1296 : PowerSeries ℚ) = 1296 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1296
lemma cm1296 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1296 : PowerSeries ℚ) * F) = 1296 * coeff m F := by
  have e : (1296 : PowerSeries ℚ) = C (1296 : ℚ) := (map_ofNat C 1296).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1620 : derivative ℚ (1620 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1620
@[simp] lemma cc1620 : constantCoeff (1620 : PowerSeries ℚ) = 1620 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1620
lemma cm1620 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1620 : PowerSeries ℚ) * F) = 1620 * coeff m F := by
  have e : (1620 : PowerSeries ℚ) = C (1620 : ℚ) := (map_ofNat C 1620).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1944 : derivative ℚ (1944 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1944
@[simp] lemma cc1944 : constantCoeff (1944 : PowerSeries ℚ) = 1944 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1944
lemma cm1944 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1944 : PowerSeries ℚ) * F) = 1944 * coeff m F := by
  have e : (1944 : PowerSeries ℚ) = C (1944 : ℚ) := (map_ofNat C 1944).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2160 : derivative ℚ (2160 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2160
@[simp] lemma cc2160 : constantCoeff (2160 : PowerSeries ℚ) = 2160 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2160
lemma cm2160 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2160 : PowerSeries ℚ) * F) = 2160 * coeff m F := by
  have e : (2160 : PowerSeries ℚ) = C (2160 : ℚ) := (map_ofNat C 2160).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2268 : derivative ℚ (2268 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2268
@[simp] lemma cc2268 : constantCoeff (2268 : PowerSeries ℚ) = 2268 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2268
lemma cm2268 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2268 : PowerSeries ℚ) * F) = 2268 * coeff m F := by
  have e : (2268 : PowerSeries ℚ) = C (2268 : ℚ) := (map_ofNat C 2268).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2445 : derivative ℚ (2445 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2445
@[simp] lemma cc2445 : constantCoeff (2445 : PowerSeries ℚ) = 2445 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2445
lemma cm2445 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2445 : PowerSeries ℚ) * F) = 2445 * coeff m F := by
  have e : (2445 : PowerSeries ℚ) = C (2445 : ℚ) := (map_ofNat C 2445).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2667 : derivative ℚ (2667 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2667
@[simp] lemma cc2667 : constantCoeff (2667 : PowerSeries ℚ) = 2667 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2667
lemma cm2667 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2667 : PowerSeries ℚ) * F) = 2667 * coeff m F := by
  have e : (2667 : PowerSeries ℚ) = C (2667 : ℚ) := (map_ofNat C 2667).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2880 : derivative ℚ (2880 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2880
@[simp] lemma cc2880 : constantCoeff (2880 : PowerSeries ℚ) = 2880 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2880
lemma cm2880 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2880 : PowerSeries ℚ) * F) = 2880 * coeff m F := by
  have e : (2880 : PowerSeries ℚ) = C (2880 : ℚ) := (map_ofNat C 2880).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3078 : derivative ℚ (3078 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3078
@[simp] lemma cc3078 : constantCoeff (3078 : PowerSeries ℚ) = 3078 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3078
lemma cm3078 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3078 : PowerSeries ℚ) * F) = 3078 * coeff m F := by
  have e : (3078 : PowerSeries ℚ) = C (3078 : ℚ) := (map_ofNat C 3078).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3582 : derivative ℚ (3582 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3582
@[simp] lemma cc3582 : constantCoeff (3582 : PowerSeries ℚ) = 3582 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3582
lemma cm3582 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3582 : PowerSeries ℚ) * F) = 3582 * coeff m F := by
  have e : (3582 : PowerSeries ℚ) = C (3582 : ℚ) := (map_ofNat C 3582).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3888 : derivative ℚ (3888 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3888
@[simp] lemma cc3888 : constantCoeff (3888 : PowerSeries ℚ) = 3888 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3888
lemma cm3888 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3888 : PowerSeries ℚ) * F) = 3888 * coeff m F := by
  have e : (3888 : PowerSeries ℚ) = C (3888 : ℚ) := (map_ofNat C 3888).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4032 : derivative ℚ (4032 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4032
@[simp] lemma cc4032 : constantCoeff (4032 : PowerSeries ℚ) = 4032 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4032
lemma cm4032 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4032 : PowerSeries ℚ) * F) = 4032 * coeff m F := by
  have e : (4032 : PowerSeries ℚ) = C (4032 : ℚ) := (map_ofNat C 4032).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4320 : derivative ℚ (4320 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4320
@[simp] lemma cc4320 : constantCoeff (4320 : PowerSeries ℚ) = 4320 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4320
lemma cm4320 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4320 : PowerSeries ℚ) * F) = 4320 * coeff m F := by
  have e : (4320 : PowerSeries ℚ) = C (4320 : ℚ) := (map_ofNat C 4320).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4536 : derivative ℚ (4536 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4536
@[simp] lemma cc4536 : constantCoeff (4536 : PowerSeries ℚ) = 4536 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4536
lemma cm4536 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4536 : PowerSeries ℚ) * F) = 4536 * coeff m F := by
  have e : (4536 : PowerSeries ℚ) = C (4536 : ℚ) := (map_ofNat C 4536).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4548 : derivative ℚ (4548 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4548
@[simp] lemma cc4548 : constantCoeff (4548 : PowerSeries ℚ) = 4548 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4548
lemma cm4548 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4548 : PowerSeries ℚ) * F) = 4548 * coeff m F := by
  have e : (4548 : PowerSeries ℚ) = C (4548 : ℚ) := (map_ofNat C 4548).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6480 : derivative ℚ (6480 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6480
@[simp] lemma cc6480 : constantCoeff (6480 : PowerSeries ℚ) = 6480 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6480
lemma cm6480 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6480 : PowerSeries ℚ) * F) = 6480 * coeff m F := by
  have e : (6480 : PowerSeries ℚ) = C (6480 : ℚ) := (map_ofNat C 6480).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6750 : derivative ℚ (6750 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6750
@[simp] lemma cc6750 : constantCoeff (6750 : PowerSeries ℚ) = 6750 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6750
lemma cm6750 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6750 : PowerSeries ℚ) * F) = 6750 * coeff m F := by
  have e : (6750 : PowerSeries ℚ) = C (6750 : ℚ) := (map_ofNat C 6750).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6804 : derivative ℚ (6804 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6804
@[simp] lemma cc6804 : constantCoeff (6804 : PowerSeries ℚ) = 6804 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6804
lemma cm6804 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6804 : PowerSeries ℚ) * F) = 6804 * coeff m F := by
  have e : (6804 : PowerSeries ℚ) = C (6804 : ℚ) := (map_ofNat C 6804).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9180 : derivative ℚ (9180 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9180
@[simp] lemma cc9180 : constantCoeff (9180 : PowerSeries ℚ) = 9180 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9180
lemma cm9180 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9180 : PowerSeries ℚ) * F) = 9180 * coeff m F := by
  have e : (9180 : PowerSeries ℚ) = C (9180 : ℚ) := (map_ofNat C 9180).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9720 : derivative ℚ (9720 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9720
@[simp] lemma cc9720 : constantCoeff (9720 : PowerSeries ℚ) = 9720 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9720
lemma cm9720 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9720 : PowerSeries ℚ) * F) = 9720 * coeff m F := by
  have e : (9720 : PowerSeries ℚ) = C (9720 : ℚ) := (map_ofNat C 9720).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11340 : derivative ℚ (11340 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11340
@[simp] lemma cc11340 : constantCoeff (11340 : PowerSeries ℚ) = 11340 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11340
lemma cm11340 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11340 : PowerSeries ℚ) * F) = 11340 * coeff m F := by
  have e : (11340 : PowerSeries ℚ) = C (11340 : ℚ) := (map_ofNat C 11340).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15363 : derivative ℚ (15363 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15363
@[simp] lemma cc15363 : constantCoeff (15363 : PowerSeries ℚ) = 15363 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15363
lemma cm15363 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15363 : PowerSeries ℚ) * F) = 15363 * coeff m F := by
  have e : (15363 : PowerSeries ℚ) = C (15363 : ℚ) := (map_ofNat C 15363).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn17172 : derivative ℚ (17172 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17172
@[simp] lemma cc17172 : constantCoeff (17172 : PowerSeries ℚ) = 17172 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17172
lemma cm17172 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17172 : PowerSeries ℚ) * F) = 17172 * coeff m F := by
  have e : (17172 : PowerSeries ℚ) = C (17172 : ℚ) := (map_ofNat C 17172).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn24156 : derivative ℚ (24156 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24156
@[simp] lemma cc24156 : constantCoeff (24156 : PowerSeries ℚ) = 24156 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24156
lemma cm24156 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24156 : PowerSeries ℚ) * F) = 24156 * coeff m F := by
  have e : (24156 : PowerSeries ℚ) = C (24156 : ℚ) := (map_ofNat C 24156).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn25272 : derivative ℚ (25272 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 25272
@[simp] lemma cc25272 : constantCoeff (25272 : PowerSeries ℚ) = 25272 := by simpa using map_natCast (constantCoeff (R := ℚ)) 25272
lemma cm25272 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((25272 : PowerSeries ℚ) * F) = 25272 * coeff m F := by
  have e : (25272 : PowerSeries ℚ) = C (25272 : ℚ) := (map_ofNat C 25272).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn25920 : derivative ℚ (25920 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 25920
@[simp] lemma cc25920 : constantCoeff (25920 : PowerSeries ℚ) = 25920 := by simpa using map_natCast (constantCoeff (R := ℚ)) 25920
lemma cm25920 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((25920 : PowerSeries ℚ) * F) = 25920 * coeff m F := by
  have e : (25920 : PowerSeries ℚ) = C (25920 : ℚ) := (map_ofNat C 25920).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn26325 : derivative ℚ (26325 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 26325
@[simp] lemma cc26325 : constantCoeff (26325 : PowerSeries ℚ) = 26325 := by simpa using map_natCast (constantCoeff (R := ℚ)) 26325
lemma cm26325 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((26325 : PowerSeries ℚ) * F) = 26325 * coeff m F := by
  have e : (26325 : PowerSeries ℚ) = C (26325 : ℚ) := (map_ofNat C 26325).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn27108 : derivative ℚ (27108 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 27108
@[simp] lemma cc27108 : constantCoeff (27108 : PowerSeries ℚ) = 27108 := by simpa using map_natCast (constantCoeff (R := ℚ)) 27108
lemma cm27108 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((27108 : PowerSeries ℚ) * F) = 27108 * coeff m F := by
  have e : (27108 : PowerSeries ℚ) = C (27108 : ℚ) := (map_ofNat C 27108).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn27216 : derivative ℚ (27216 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 27216
@[simp] lemma cc27216 : constantCoeff (27216 : PowerSeries ℚ) = 27216 := by simpa using map_natCast (constantCoeff (R := ℚ)) 27216
lemma cm27216 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((27216 : PowerSeries ℚ) * F) = 27216 * coeff m F := by
  have e : (27216 : PowerSeries ℚ) = C (27216 : ℚ) := (map_ofNat C 27216).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn29484 : derivative ℚ (29484 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 29484
@[simp] lemma cc29484 : constantCoeff (29484 : PowerSeries ℚ) = 29484 := by simpa using map_natCast (constantCoeff (R := ℚ)) 29484
lemma cm29484 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((29484 : PowerSeries ℚ) * F) = 29484 * coeff m F := by
  have e : (29484 : PowerSeries ℚ) = C (29484 : ℚ) := (map_ofNat C 29484).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn47250 : derivative ℚ (47250 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 47250
@[simp] lemma cc47250 : constantCoeff (47250 : PowerSeries ℚ) = 47250 := by simpa using map_natCast (constantCoeff (R := ℚ)) 47250
lemma cm47250 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((47250 : PowerSeries ℚ) * F) = 47250 * coeff m F := by
  have e : (47250 : PowerSeries ℚ) = C (47250 : ℚ) := (map_ofNat C 47250).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn103518 : derivative ℚ (103518 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 103518
@[simp] lemma cc103518 : constantCoeff (103518 : PowerSeries ℚ) = 103518 := by simpa using map_natCast (constantCoeff (R := ℚ)) 103518
lemma cm103518 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((103518 : PowerSeries ℚ) * F) = 103518 * coeff m F := by
  have e : (103518 : PowerSeries ℚ) = C (103518 : ℚ) := (map_ofNat C 103518).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn131220 : derivative ℚ (131220 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 131220
@[simp] lemma cc131220 : constantCoeff (131220 : PowerSeries ℚ) = 131220 := by simpa using map_natCast (constantCoeff (R := ℚ)) 131220
lemma cm131220 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((131220 : PowerSeries ℚ) * F) = 131220 * coeff m F := by
  have e : (131220 : PowerSeries ℚ) = C (131220 : ℚ) := (map_ofNat C 131220).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn132678 : derivative ℚ (132678 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 132678
@[simp] lemma cc132678 : constantCoeff (132678 : PowerSeries ℚ) = 132678 := by simpa using map_natCast (constantCoeff (R := ℚ)) 132678
lemma cm132678 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((132678 : PowerSeries ℚ) * F) = 132678 * coeff m F := by
  have e : (132678 : PowerSeries ℚ) = C (132678 : ℚ) := (map_ofNat C 132678).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn164880 : derivative ℚ (164880 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 164880
@[simp] lemma cc164880 : constantCoeff (164880 : PowerSeries ℚ) = 164880 := by simpa using map_natCast (constantCoeff (R := ℚ)) 164880
lemma cm164880 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((164880 : PowerSeries ℚ) * F) = 164880 * coeff m F := by
  have e : (164880 : PowerSeries ℚ) = C (164880 : ℚ) := (map_ofNat C 164880).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn174150 : derivative ℚ (174150 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 174150
@[simp] lemma cc174150 : constantCoeff (174150 : PowerSeries ℚ) = 174150 := by simpa using map_natCast (constantCoeff (R := ℚ)) 174150
lemma cm174150 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((174150 : PowerSeries ℚ) * F) = 174150 * coeff m F := by
  have e : (174150 : PowerSeries ℚ) = C (174150 : ℚ) := (map_ofNat C 174150).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn193536 : derivative ℚ (193536 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 193536
@[simp] lemma cc193536 : constantCoeff (193536 : PowerSeries ℚ) = 193536 := by simpa using map_natCast (constantCoeff (R := ℚ)) 193536
lemma cm193536 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((193536 : PowerSeries ℚ) * F) = 193536 * coeff m F := by
  have e : (193536 : PowerSeries ℚ) = C (193536 : ℚ) := (map_ofNat C 193536).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn200448 : derivative ℚ (200448 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 200448
@[simp] lemma cc200448 : constantCoeff (200448 : PowerSeries ℚ) = 200448 := by simpa using map_natCast (constantCoeff (R := ℚ)) 200448
lemma cm200448 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((200448 : PowerSeries ℚ) * F) = 200448 * coeff m F := by
  have e : (200448 : PowerSeries ℚ) = C (200448 : ℚ) := (map_ofNat C 200448).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn226125 : derivative ℚ (226125 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 226125
@[simp] lemma cc226125 : constantCoeff (226125 : PowerSeries ℚ) = 226125 := by simpa using map_natCast (constantCoeff (R := ℚ)) 226125
lemma cm226125 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((226125 : PowerSeries ℚ) * F) = 226125 * coeff m F := by
  have e : (226125 : PowerSeries ℚ) = C (226125 : ℚ) := (map_ofNat C 226125).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn753300 : derivative ℚ (753300 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 753300
@[simp] lemma cc753300 : constantCoeff (753300 : PowerSeries ℚ) = 753300 := by simpa using map_natCast (constantCoeff (R := ℚ)) 753300
lemma cm753300 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((753300 : PowerSeries ℚ) * F) = 753300 * coeff m F := by
  have e : (753300 : PowerSeries ℚ) = C (753300 : ℚ) := (map_ofNat C 753300).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn777600 : derivative ℚ (777600 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 777600
@[simp] lemma cc777600 : constantCoeff (777600 : PowerSeries ℚ) = 777600 := by simpa using map_natCast (constantCoeff (R := ℚ)) 777600
lemma cm777600 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((777600 : PowerSeries ℚ) * F) = 777600 * coeff m F := by
  have e : (777600 : PowerSeries ℚ) = C (777600 : ℚ) := (map_ofNat C 777600).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1108215 : derivative ℚ (1108215 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1108215
@[simp] lemma cc1108215 : constantCoeff (1108215 : PowerSeries ℚ) = 1108215 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1108215
lemma cm1108215 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1108215 : PowerSeries ℚ) * F) = 1108215 * coeff m F := by
  have e : (1108215 : PowerSeries ℚ) = C (1108215 : ℚ) := (map_ofNat C 1108215).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1640250 : derivative ℚ (1640250 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1640250
@[simp] lemma cc1640250 : constantCoeff (1640250 : PowerSeries ℚ) = 1640250 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1640250
lemma cm1640250 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1640250 : PowerSeries ℚ) * F) = 1640250 * coeff m F := by
  have e : (1640250 : PowerSeries ℚ) = C (1640250 : ℚ) := (map_ofNat C 1640250).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1646325 : derivative ℚ (1646325 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1646325
@[simp] lemma cc1646325 : constantCoeff (1646325 : PowerSeries ℚ) = 1646325 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1646325
lemma cm1646325 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1646325 : PowerSeries ℚ) * F) = 1646325 * coeff m F := by
  have e : (1646325 : PowerSeries ℚ) = C (1646325 : ℚ) := (map_ofNat C 1646325).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2370060 : derivative ℚ (2370060 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2370060
@[simp] lemma cc2370060 : constantCoeff (2370060 : PowerSeries ℚ) = 2370060 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2370060
lemma cm2370060 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2370060 : PowerSeries ℚ) * F) = 2370060 * coeff m F := by
  have e : (2370060 : PowerSeries ℚ) = C (2370060 : ℚ) := (map_ofNat C 2370060).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2733750 : derivative ℚ (2733750 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2733750
@[simp] lemma cc2733750 : constantCoeff (2733750 : PowerSeries ℚ) = 2733750 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2733750
lemma cm2733750 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2733750 : PowerSeries ℚ) * F) = 2733750 * coeff m F := by
  have e : (2733750 : PowerSeries ℚ) = C (2733750 : ℚ) := (map_ofNat C 2733750).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2855250 : derivative ℚ (2855250 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2855250
@[simp] lemma cc2855250 : constantCoeff (2855250 : PowerSeries ℚ) = 2855250 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2855250
lemma cm2855250 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2855250 : PowerSeries ℚ) * F) = 2855250 * coeff m F := by
  have e : (2855250 : PowerSeries ℚ) = C (2855250 : ℚ) := (map_ofNat C 2855250).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4514940 : derivative ℚ (4514940 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4514940
@[simp] lemma cc4514940 : constantCoeff (4514940 : PowerSeries ℚ) = 4514940 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4514940
lemma cm4514940 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4514940 : PowerSeries ℚ) * F) = 4514940 * coeff m F := by
  have e : (4514940 : PowerSeries ℚ) = C (4514940 : ℚ) := (map_ofNat C 4514940).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5133375 : derivative ℚ (5133375 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5133375
@[simp] lemma cc5133375 : constantCoeff (5133375 : PowerSeries ℚ) = 5133375 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5133375
lemma cm5133375 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5133375 : PowerSeries ℚ) * F) = 5133375 * coeff m F := by
  have e : (5133375 : PowerSeries ℚ) = C (5133375 : ℚ) := (map_ofNat C 5133375).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9185400 : derivative ℚ (9185400 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9185400
@[simp] lemma cc9185400 : constantCoeff (9185400 : PowerSeries ℚ) = 9185400 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9185400
lemma cm9185400 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9185400 : PowerSeries ℚ) * F) = 9185400 * coeff m F := by
  have e : (9185400 : PowerSeries ℚ) = C (9185400 : ℚ) := (map_ofNat C 9185400).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn12484125 : derivative ℚ (12484125 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 12484125
@[simp] lemma cc12484125 : constantCoeff (12484125 : PowerSeries ℚ) = 12484125 := by simpa using map_natCast (constantCoeff (R := ℚ)) 12484125
lemma cm12484125 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((12484125 : PowerSeries ℚ) * F) = 12484125 * coeff m F := by
  have e : (12484125 : PowerSeries ℚ) = C (12484125 : ℚ) := (map_ofNat C 12484125).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14580000 : derivative ℚ (14580000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14580000
@[simp] lemma cc14580000 : constantCoeff (14580000 : PowerSeries ℚ) = 14580000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14580000
lemma cm14580000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14580000 : PowerSeries ℚ) * F) = 14580000 * coeff m F := by
  have e : (14580000 : PowerSeries ℚ) = C (14580000 : ℚ) := (map_ofNat C 14580000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16685109 : derivative ℚ (16685109 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16685109
@[simp] lemma cc16685109 : constantCoeff (16685109 : PowerSeries ℚ) = 16685109 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16685109
lemma cm16685109 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16685109 : PowerSeries ℚ) * F) = 16685109 * coeff m F := by
  have e : (16685109 : PowerSeries ℚ) = C (16685109 : ℚ) := (map_ofNat C 16685109).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn24986475 : derivative ℚ (24986475 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24986475
@[simp] lemma cc24986475 : constantCoeff (24986475 : PowerSeries ℚ) = 24986475 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24986475
lemma cm24986475 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24986475 : PowerSeries ℚ) * F) = 24986475 * coeff m F := by
  have e : (24986475 : PowerSeries ℚ) = C (24986475 : ℚ) := (map_ofNat C 24986475).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn35870445 : derivative ℚ (35870445 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 35870445
@[simp] lemma cc35870445 : constantCoeff (35870445 : PowerSeries ℚ) = 35870445 := by simpa using map_natCast (constantCoeff (R := ℚ)) 35870445
lemma cm35870445 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((35870445 : PowerSeries ℚ) * F) = 35870445 * coeff m F := by
  have e : (35870445 : PowerSeries ℚ) = C (35870445 : ℚ) := (map_ofNat C 35870445).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn35919531 : derivative ℚ (35919531 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 35919531
@[simp] lemma cc35919531 : constantCoeff (35919531 : PowerSeries ℚ) = 35919531 := by simpa using map_natCast (constantCoeff (R := ℚ)) 35919531
lemma cm35919531 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((35919531 : PowerSeries ℚ) * F) = 35919531 * coeff m F := by
  have e : (35919531 : PowerSeries ℚ) = C (35919531 : ℚ) := (map_ofNat C 35919531).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn39366000 : derivative ℚ (39366000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 39366000
@[simp] lemma cc39366000 : constantCoeff (39366000 : PowerSeries ℚ) = 39366000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 39366000
lemma cm39366000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((39366000 : PowerSeries ℚ) * F) = 39366000 * coeff m F := by
  have e : (39366000 : PowerSeries ℚ) = C (39366000 : ℚ) := (map_ofNat C 39366000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn43320825 : derivative ℚ (43320825 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 43320825
@[simp] lemma cc43320825 : constantCoeff (43320825 : PowerSeries ℚ) = 43320825 := by simpa using map_natCast (constantCoeff (R := ℚ)) 43320825
lemma cm43320825 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((43320825 : PowerSeries ℚ) * F) = 43320825 * coeff m F := by
  have e : (43320825 : PowerSeries ℚ) = C (43320825 : ℚ) := (map_ofNat C 43320825).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn44104500 : derivative ℚ (44104500 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 44104500
@[simp] lemma cc44104500 : constantCoeff (44104500 : PowerSeries ℚ) = 44104500 := by simpa using map_natCast (constantCoeff (R := ℚ)) 44104500
lemma cm44104500 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((44104500 : PowerSeries ℚ) * F) = 44104500 * coeff m F := by
  have e : (44104500 : PowerSeries ℚ) = C (44104500 : ℚ) := (map_ofNat C 44104500).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn55112400 : derivative ℚ (55112400 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 55112400
@[simp] lemma cc55112400 : constantCoeff (55112400 : PowerSeries ℚ) = 55112400 := by simpa using map_natCast (constantCoeff (R := ℚ)) 55112400
lemma cm55112400 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((55112400 : PowerSeries ℚ) * F) = 55112400 * coeff m F := by
  have e : (55112400 : PowerSeries ℚ) = C (55112400 : ℚ) := (map_ofNat C 55112400).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn59125545 : derivative ℚ (59125545 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 59125545
@[simp] lemma cc59125545 : constantCoeff (59125545 : PowerSeries ℚ) = 59125545 := by simpa using map_natCast (constantCoeff (R := ℚ)) 59125545
lemma cm59125545 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((59125545 : PowerSeries ℚ) * F) = 59125545 * coeff m F := by
  have e : (59125545 : PowerSeries ℚ) = C (59125545 : ℚ) := (map_ofNat C 59125545).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn59876415 : derivative ℚ (59876415 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 59876415
@[simp] lemma cc59876415 : constantCoeff (59876415 : PowerSeries ℚ) = 59876415 := by simpa using map_natCast (constantCoeff (R := ℚ)) 59876415
lemma cm59876415 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((59876415 : PowerSeries ℚ) * F) = 59876415 * coeff m F := by
  have e : (59876415 : PowerSeries ℚ) = C (59876415 : ℚ) := (map_ofNat C 59876415).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn62985600 : derivative ℚ (62985600 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 62985600
@[simp] lemma cc62985600 : constantCoeff (62985600 : PowerSeries ℚ) = 62985600 := by simpa using map_natCast (constantCoeff (R := ℚ)) 62985600
lemma cm62985600 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((62985600 : PowerSeries ℚ) * F) = 62985600 * coeff m F := by
  have e : (62985600 : PowerSeries ℚ) = C (62985600 : ℚ) := (map_ofNat C 62985600).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn87480000 : derivative ℚ (87480000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 87480000
@[simp] lemma cc87480000 : constantCoeff (87480000 : PowerSeries ℚ) = 87480000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 87480000
lemma cm87480000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((87480000 : PowerSeries ℚ) * F) = 87480000 * coeff m F := by
  have e : (87480000 : PowerSeries ℚ) = C (87480000 : ℚ) := (map_ofNat C 87480000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn94478400 : derivative ℚ (94478400 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 94478400
@[simp] lemma cc94478400 : constantCoeff (94478400 : PowerSeries ℚ) = 94478400 := by simpa using map_natCast (constantCoeff (R := ℚ)) 94478400
lemma cm94478400 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((94478400 : PowerSeries ℚ) * F) = 94478400 * coeff m F := by
  have e : (94478400 : PowerSeries ℚ) = C (94478400 : ℚ) := (map_ofNat C 94478400).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn134063100 : derivative ℚ (134063100 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 134063100
@[simp] lemma cc134063100 : constantCoeff (134063100 : PowerSeries ℚ) = 134063100 := by simpa using map_natCast (constantCoeff (R := ℚ)) 134063100
lemma cm134063100 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((134063100 : PowerSeries ℚ) * F) = 134063100 * coeff m F := by
  have e : (134063100 : PowerSeries ℚ) = C (134063100 : ℚ) := (map_ofNat C 134063100).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn170061120 : derivative ℚ (170061120 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 170061120
@[simp] lemma cc170061120 : constantCoeff (170061120 : PowerSeries ℚ) = 170061120 := by simpa using map_natCast (constantCoeff (R := ℚ)) 170061120
lemma cm170061120 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((170061120 : PowerSeries ℚ) * F) = 170061120 * coeff m F := by
  have e : (170061120 : PowerSeries ℚ) = C (170061120 : ℚ) := (map_ofNat C 170061120).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn205578000 : derivative ℚ (205578000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 205578000
@[simp] lemma cc205578000 : constantCoeff (205578000 : PowerSeries ℚ) = 205578000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 205578000
lemma cm205578000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((205578000 : PowerSeries ℚ) * F) = 205578000 * coeff m F := by
  have e : (205578000 : PowerSeries ℚ) = C (205578000 : ℚ) := (map_ofNat C 205578000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn207852480 : derivative ℚ (207852480 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 207852480
@[simp] lemma cc207852480 : constantCoeff (207852480 : PowerSeries ℚ) = 207852480 := by simpa using map_natCast (constantCoeff (R := ℚ)) 207852480
lemma cm207852480 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((207852480 : PowerSeries ℚ) * F) = 207852480 * coeff m F := by
  have e : (207852480 : PowerSeries ℚ) = C (207852480 : ℚ) := (map_ofNat C 207852480).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn246116232 : derivative ℚ (246116232 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 246116232
@[simp] lemma cc246116232 : constantCoeff (246116232 : PowerSeries ℚ) = 246116232 := by simpa using map_natCast (constantCoeff (R := ℚ)) 246116232
lemma cm246116232 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((246116232 : PowerSeries ℚ) * F) = 246116232 * coeff m F := by
  have e : (246116232 : PowerSeries ℚ) = C (246116232 : ℚ) := (map_ofNat C 246116232).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn313659540 : derivative ℚ (313659540 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 313659540
@[simp] lemma cc313659540 : constantCoeff (313659540 : PowerSeries ℚ) = 313659540 := by simpa using map_natCast (constantCoeff (R := ℚ)) 313659540
lemma cm313659540 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((313659540 : PowerSeries ℚ) * F) = 313659540 * coeff m F := by
  have e : (313659540 : PowerSeries ℚ) = C (313659540 : ℚ) := (map_ofNat C 313659540).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn555561423 : derivative ℚ (555561423 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 555561423
@[simp] lemma cc555561423 : constantCoeff (555561423 : PowerSeries ℚ) = 555561423 := by simpa using map_natCast (constantCoeff (R := ℚ)) 555561423
lemma cm555561423 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((555561423 : PowerSeries ℚ) * F) = 555561423 * coeff m F := by
  have e : (555561423 : PowerSeries ℚ) = C (555561423 : ℚ) := (map_ofNat C 555561423).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn914297220 : derivative ℚ (914297220 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 914297220
@[simp] lemma cc914297220 : constantCoeff (914297220 : PowerSeries ℚ) = 914297220 := by simpa using map_natCast (constantCoeff (R := ℚ)) 914297220
lemma cm914297220 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((914297220 : PowerSeries ℚ) * F) = 914297220 * coeff m F := by
  have e : (914297220 : PowerSeries ℚ) = C (914297220 : ℚ) := (map_ofNat C 914297220).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1032438960 : derivative ℚ (1032438960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1032438960
@[simp] lemma cc1032438960 : constantCoeff (1032438960 : PowerSeries ℚ) = 1032438960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1032438960
lemma cm1032438960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1032438960 : PowerSeries ℚ) * F) = 1032438960 * coeff m F := by
  have e : (1032438960 : PowerSeries ℚ) = C (1032438960 : ℚ) := (map_ofNat C 1032438960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1302542208 : derivative ℚ (1302542208 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1302542208
@[simp] lemma cc1302542208 : constantCoeff (1302542208 : PowerSeries ℚ) = 1302542208 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1302542208
lemma cm1302542208 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1302542208 : PowerSeries ℚ) * F) = 1302542208 * coeff m F := by
  have e : (1302542208 : PowerSeries ℚ) = C (1302542208 : ℚ) := (map_ofNat C 1302542208).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1990344960 : derivative ℚ (1990344960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1990344960
@[simp] lemma cc1990344960 : constantCoeff (1990344960 : PowerSeries ℚ) = 1990344960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1990344960
lemma cm1990344960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1990344960 : PowerSeries ℚ) * F) = 1990344960 * coeff m F := by
  have e : (1990344960 : PowerSeries ℚ) = C (1990344960 : ℚ) := (map_ofNat C 1990344960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2331726912 : derivative ℚ (2331726912 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2331726912
@[simp] lemma cc2331726912 : constantCoeff (2331726912 : PowerSeries ℚ) = 2331726912 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2331726912
lemma cm2331726912 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2331726912 : PowerSeries ℚ) * F) = 2331726912 * coeff m F := by
  have e : (2331726912 : PowerSeries ℚ) = C (2331726912 : ℚ) := (map_ofNat C 2331726912).symm
  rw [e, coeff_C_mul]

lemma S_sq : S * S = R := by
  have := bs_sq (R - 1) (by simp [R])
  unfold S; rw [this]; ring

noncomputable def DD : PowerSeries ℚ := 18
noncomputable def NN : PowerSeries ℚ := 1 - 6 * X + 18 * X ^ 2 - 27 * X ^ 3 + (-1 + 3 * X - 9 * X ^ 2) * S
noncomputable def AA : PowerSeries ℚ := NN * DD⁻¹

lemma hA : AA * DD = NN := by
  unfold AA
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [DD]), mul_one]

lemma hdD : derivative ℚ DD = 0 := by
  simp [DD] <;> ring
lemma hdR : derivative ℚ R = -144*X^3 + 18*X - 6 := by
  simp [R] <;> ring
lemma hdN : derivative ℚ NN = -81*X^2 + 36*X - 6 + (3 - 18*X) * S + (-9*X^2 + 3*X - 1) * derivative ℚ S := by
  simp [NN] <;> ring

lemma ode1 : ((-1) * X ^ 0 + (9) * X ^ 1 + (-36) * X ^ 2 + (81) * X ^ 3 + (-45) * X ^ 4 + (-108) * X ^ 5 + (324) * X ^ 6 : PowerSeries ℚ) * derivative ℚ AA + ((-6) * X ^ 0 + (54) * X ^ 1 + (-189) * X ^ 2 + (171) * X ^ 3 + (324) * X ^ 4 + (-1296) * X ^ 5 : PowerSeries ℚ) * AA = ((-4) * X ^ 3 + (30) * X ^ 4 + (-144) * X ^ 5 + (378) * X ^ 6 + (-648) * X ^ 7 + (486) * X ^ 8 : PowerSeries ℚ) := by
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
  linear_combination (1679616*X^9 - 419904*X^8 - 641520*X^7 + 629856*X^6 - 131220*X^5 - 78732*X^4 + 64476*X^3 - 20412*X^2 + 3240*X - 216) * r1 + (-419904*X^10 + 139968*X^9 + 163296*X^8 - 209952*X^7 + 67068*X^6 + 20412*X^5 - 29484*X^4 + 13608*X^3 - 3564*X^2 + 540*X - 36) * r2 + (-52488*X^8 + 34992*X^7 - 4374*X^6 - 13608*X^5 + 11016*X^4 - 4860*X^3 + 1296*X^2 - 216*X + 18) * r4

lemma hdV : derivative ℚ ((-1) * X ^ 0 + (9) * X ^ 1 + (-36) * X ^ 2 + (81) * X ^ 3 + (-45) * X ^ 4 + (-108) * X ^ 5 + (324) * X ^ 6 : PowerSeries ℚ) = ((9) * X ^ 0 + (-72) * X ^ 1 + (243) * X ^ 2 + (-180) * X ^ 3 + (-540) * X ^ 4 + (1944) * X ^ 5 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdU : derivative ℚ ((-6) * X ^ 0 + (54) * X ^ 1 + (-189) * X ^ 2 + (171) * X ^ 3 + (324) * X ^ 4 + (-1296) * X ^ 5 : PowerSeries ℚ) = ((54) * X ^ 0 + (-378) * X ^ 1 + (513) * X ^ 2 + (1296) * X ^ 3 + (-6480) * X ^ 4 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdW : derivative ℚ ((-4) * X ^ 3 + (30) * X ^ 4 + (-144) * X ^ 5 + (378) * X ^ 6 + (-648) * X ^ 7 + (486) * X ^ 8 : PowerSeries ℚ) = ((-12) * X ^ 2 + (120) * X ^ 3 + (-720) * X ^ 4 + (2268) * X ^ 5 + (-4536) * X ^ 6 + (3888) * X ^ 7 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdV1 : derivative ℚ ((9) * X ^ 0 + (-72) * X ^ 1 + (243) * X ^ 2 + (-180) * X ^ 3 + (-540) * X ^ 4 + (1944) * X ^ 5 : PowerSeries ℚ) = ((-72) * X ^ 0 + (486) * X ^ 1 + (-540) * X ^ 2 + (-2160) * X ^ 3 + (9720) * X ^ 4 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdU1 : derivative ℚ ((54) * X ^ 0 + (-378) * X ^ 1 + (513) * X ^ 2 + (1296) * X ^ 3 + (-6480) * X ^ 4 : PowerSeries ℚ) = ((-378) * X ^ 0 + (1026) * X ^ 1 + (3888) * X ^ 2 + (-25920) * X ^ 3 : PowerSeries ℚ) := by
  simp <;> ring
lemma hdW1 : derivative ℚ ((-12) * X ^ 2 + (120) * X ^ 3 + (-720) * X ^ 4 + (2268) * X ^ 5 + (-4536) * X ^ 6 + (3888) * X ^ 7 : PowerSeries ℚ) = ((-24) * X ^ 1 + (360) * X ^ 2 + (-2880) * X ^ 3 + (11340) * X ^ 4 + (-27216) * X ^ 5 + (27216) * X ^ 6 : PowerSeries ℚ) := by
  simp <;> ring

lemma dmul (F G : PowerSeries ℚ) : derivative ℚ (F * G) = F * derivative ℚ G + G * derivative ℚ F := by
  rw [Derivation.leibniz]; simp only [smul_eq_mul]

lemma ode2 : ((9) * X ^ 0 + (-72) * X ^ 1 + (243) * X ^ 2 + (-180) * X ^ 3 + (-540) * X ^ 4 + (1944) * X ^ 5 : PowerSeries ℚ) * derivative ℚ AA + ((-1) * X ^ 0 + (9) * X ^ 1 + (-36) * X ^ 2 + (81) * X ^ 3 + (-45) * X ^ 4 + (-108) * X ^ 5 + (324) * X ^ 6 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((54) * X ^ 0 + (-378) * X ^ 1 + (513) * X ^ 2 + (1296) * X ^ 3 + (-6480) * X ^ 4 : PowerSeries ℚ) * AA + ((-6) * X ^ 0 + (54) * X ^ 1 + (-189) * X ^ 2 + (171) * X ^ 3 + (324) * X ^ 4 + (-1296) * X ^ 5 : PowerSeries ℚ) * derivative ℚ AA = ((-12) * X ^ 2 + (120) * X ^ 3 + (-720) * X ^ 4 + (2268) * X ^ 5 + (-4536) * X ^ 6 + (3888) * X ^ 7 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) ode1
  rw [map_add, dmul, dmul, hdV, hdU, hdW] at h
  linear_combination h

lemma ode3' : ((-72) * X ^ 0 + (486) * X ^ 1 + (-540) * X ^ 2 + (-2160) * X ^ 3 + (9720) * X ^ 4 : PowerSeries ℚ) * derivative ℚ AA + ((9) * X ^ 0 + (-72) * X ^ 1 + (243) * X ^ 2 + (-180) * X ^ 3 + (-540) * X ^ 4 + (1944) * X ^ 5 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + (((9) * X ^ 0 + (-72) * X ^ 1 + (243) * X ^ 2 + (-180) * X ^ 3 + (-540) * X ^ 4 + (1944) * X ^ 5 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((-1) * X ^ 0 + (9) * X ^ 1 + (-36) * X ^ 2 + (81) * X ^ 3 + (-45) * X ^ 4 + (-108) * X ^ 5 + (324) * X ^ 6 : PowerSeries ℚ) * derivative ℚ (derivative ℚ (derivative ℚ AA))) + (((-378) * X ^ 0 + (1026) * X ^ 1 + (3888) * X ^ 2 + (-25920) * X ^ 3 : PowerSeries ℚ) * AA + ((54) * X ^ 0 + (-378) * X ^ 1 + (513) * X ^ 2 + (1296) * X ^ 3 + (-6480) * X ^ 4 : PowerSeries ℚ) * derivative ℚ AA) + (((54) * X ^ 0 + (-378) * X ^ 1 + (513) * X ^ 2 + (1296) * X ^ 3 + (-6480) * X ^ 4 : PowerSeries ℚ) * derivative ℚ AA + ((-6) * X ^ 0 + (54) * X ^ 1 + (-189) * X ^ 2 + (171) * X ^ 3 + (324) * X ^ 4 + (-1296) * X ^ 5 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA)) = ((-24) * X ^ 1 + (360) * X ^ 2 + (-2880) * X ^ 3 + (11340) * X ^ 4 + (-27216) * X ^ 5 + (27216) * X ^ 6 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) ode2
  rw [map_add, map_add, map_add, dmul, dmul, dmul, dmul, hdV1, hdV, hdU1, hdU, hdW1] at h
  linear_combination h

lemma ode3 : ((4032) * X ^ 1 + (-25272) * X ^ 2 + (29484) * X ^ 3 + (200448) * X ^ 4 : PowerSeries ℚ) * AA + ((672) * X ^ 1 + (-3582) * X ^ 2 + (3078) * X ^ 3 + (-17172) * X ^ 5 : PowerSeries ℚ) * derivative ℚ AA + ((105) * X ^ 2 + (-855) * X ^ 3 + (1620) * X ^ 4 + (-9180) * X ^ 6 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((25) * X ^ 3 + (-150) * X ^ 4 + (225) * X ^ 5 + (-900) * X ^ 7 : PowerSeries ℚ) * derivative ℚ (derivative ℚ (derivative ℚ AA)) = ((4548) * X ^ 4 + (-24156) * X ^ 5 + (103518) * X ^ 6 + (-132678) * X ^ 7 : PowerSeries ℚ) := by
  have e1 := ode1
  have e2 := ode2
  have e3 := ode3'
  have hK : (((-1) * X ^ 0 + (9) * X ^ 1 + (-36) * X ^ 2 + (81) * X ^ 3 + (-45) * X ^ 4 + (-108) * X ^ 5 + (324) * X ^ 6 : PowerSeries ℚ) ^ 3 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  apply mul_left_cancel₀ hK
  linear_combination (((25) * X ^ 3 + (-600) * X ^ 4 + (6750) * X ^ 5 + (-47250) * X ^ 6 + (226125) * X ^ 7 + (-753300) * X ^ 8 + (1646325) * X ^ 9 + (-1640250) * X ^ 10 + (-2855250) * X ^ 11 + (14580000) * X ^ 12 + (-24986475) * X ^ 13 + (9185400) * X ^ 14 + (44104500) * X ^ 15 + (-87480000) * X ^ 16 + (39366000) * X ^ 17 + (62985600) * X ^ 18 + (-94478400) * X ^ 19 : PowerSeries ℚ)) * e3 + (((105) * X ^ 2 + (-2445) * X ^ 3 + (26325) * X ^ 4 + (-174150) * X ^ 5 + (777600) * X ^ 6 + (-2370060) * X ^ 7 + (4514940) * X ^ 8 + (-2733750) * X ^ 9 + (-12484125) * X ^ 10 + (43320825) * X ^ 11 + (-59125545) * X ^ 12 + (-131220) * X ^ 13 + (134063100) * X ^ 14 + (-205578000) * X ^ 15 + (55112400) * X ^ 16 + (170061120) * X ^ 17 + (-207852480) * X ^ 18 : PowerSeries ℚ)) * e2 + (((672) * X ^ 1 + (-15363) * X ^ 2 + (164880) * X ^ 3 + (-1108215) * X ^ 4 + (5133375) * X ^ 5 + (-16685109) * X ^ 6 + (35919531) * X ^ 7 + (-35870445) * X ^ 8 + (-59876415) * X ^ 9 + (313659540) * X ^ 10 + (-555561423) * X ^ 11 + (246116232) * X ^ 12 + (914297220) * X ^ 13 + (-1990344960) * X ^ 14 + (1032438960) * X ^ 15 + (1302542208) * X ^ 16 + (-2331726912) * X ^ 17 : PowerSeries ℚ)) * e1

lemma ha (n : ℕ) : a n = coeff (n + 4) AA := rfl

lemma rec_a (k : ℕ) : (25*((k + 4 : ℕ) : ℚ)^3 + 330*((k + 4 : ℕ) : ℚ)^2 + 2057*((k + 4 : ℕ) : ℚ) + 4548) * a (k + 4) + (-150*((k + 4 : ℕ) : ℚ)^3 - 1755*((k + 4 : ℕ) : ℚ)^2 - 9507*((k + 4 : ℕ) : ℚ) - 12744) * a (k + 3) + (225*((k + 4 : ℕ) : ℚ)^3 + 2295*((k + 4 : ℕ) : ℚ)^2 + 8388*((k + 4 : ℕ) : ℚ) - 15876) * a (k + 2) + (29484) * a (k + 1) + (-900*((k + 4 : ℕ) : ℚ)^3 - 6480*((k + 4 : ℕ) : ℚ)^2 - 9792*((k + 4 : ℕ) : ℚ) + 200448) * a (k + 0) = 0 := by
  have h := congrArg (coeff (k + 8)) ode3
  simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm13, cm14, cm15, cm16, cm17, cm18, cm19, cm24, cm25, cm27, cm30, cm36, cm45, cm54, cm72, cm81, cm105, cm108, cm120, cm144, cm150, cm171, cm180, cm189, cm216, cm225, cm243, cm324, cm360, cm378, cm405, cm486, cm513, cm540, cm600, cm617, cm648, cm672, cm720, cm828, cm855, cm900, cm1026, cm1152, cm1296, cm1620, cm1944, cm2160, cm2268, cm2445, cm2667, cm2880, cm3078, cm3582, cm3888, cm4032, cm4320, cm4536, cm4548, cm6480, cm6750, cm6804, cm9180, cm9720, cm11340, cm15363, cm17172, cm24156, cm25272, cm25920, cm26325, cm27108, cm27216, cm29484, cm47250, cm103518, cm131220, cm132678, cm164880, cm174150, cm193536, cm200448, cm226125, cm753300, cm777600, cm1108215, cm1640250, cm1646325, cm2370060, cm2733750, cm2855250, cm4514940, cm5133375, cm9185400, cm12484125, cm14580000, cm16685109, cm24986475, cm35870445, cm35919531, cm39366000, cm43320825, cm44104500, cm55112400, cm59125545, cm59876415, cm62985600, cm87480000, cm94478400, cm134063100, cm170061120, cm205578000, cm207852480, cm246116232, cm313659540, cm555561423, cm914297220, cm1032438960, cm1302542208, cm1990344960, cm2331726912, coeff_X_pow_mul', coeff_derivative] at h
  simp [PowerSeries.coeff_X] at h
  simp only [ha]
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at h ⊢
  push_cast at h ⊢
  try simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
  linear_combination h

end OMA.S_oeis_a126322

theorem OMA.solution : type_of% @OMA.S_oeis_a126322.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega, show k + 4 - 4 = k + 0 from by omega]
  have h := OMA.S_oeis_a126322.rec_a k
  push_cast at h ⊢
  linear_combination h
