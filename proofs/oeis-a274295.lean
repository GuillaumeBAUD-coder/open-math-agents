import OMAStatements.S_oeis_a274295
import Mathlib

namespace OMA.S_oeis_a274295

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
@[simp] lemma dn20 : derivative ℚ (20 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20
@[simp] lemma cc20 : constantCoeff (20 : PowerSeries ℚ) = 20 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20
lemma cm20 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20 : PowerSeries ℚ) * F) = 20 * coeff m F := by
  have e : (20 : PowerSeries ℚ) = C (20 : ℚ) := (map_ofNat C 20).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn24 : derivative ℚ (24 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24
@[simp] lemma cc24 : constantCoeff (24 : PowerSeries ℚ) = 24 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24
lemma cm24 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24 : PowerSeries ℚ) * F) = 24 * coeff m F := by
  have e : (24 : PowerSeries ℚ) = C (24 : ℚ) := (map_ofNat C 24).symm
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
@[simp] lemma dn32 : derivative ℚ (32 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32
@[simp] lemma cc32 : constantCoeff (32 : PowerSeries ℚ) = 32 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32
lemma cm32 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32 : PowerSeries ℚ) * F) = 32 * coeff m F := by
  have e : (32 : PowerSeries ℚ) = C (32 : ℚ) := (map_ofNat C 32).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn34 : derivative ℚ (34 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 34
@[simp] lemma cc34 : constantCoeff (34 : PowerSeries ℚ) = 34 := by simpa using map_natCast (constantCoeff (R := ℚ)) 34
lemma cm34 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((34 : PowerSeries ℚ) * F) = 34 * coeff m F := by
  have e : (34 : PowerSeries ℚ) = C (34 : ℚ) := (map_ofNat C 34).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn37 : derivative ℚ (37 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 37
@[simp] lemma cc37 : constantCoeff (37 : PowerSeries ℚ) = 37 := by simpa using map_natCast (constantCoeff (R := ℚ)) 37
lemma cm37 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((37 : PowerSeries ℚ) * F) = 37 * coeff m F := by
  have e : (37 : PowerSeries ℚ) = C (37 : ℚ) := (map_ofNat C 37).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn39 : derivative ℚ (39 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 39
@[simp] lemma cc39 : constantCoeff (39 : PowerSeries ℚ) = 39 := by simpa using map_natCast (constantCoeff (R := ℚ)) 39
lemma cm39 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((39 : PowerSeries ℚ) * F) = 39 * coeff m F := by
  have e : (39 : PowerSeries ℚ) = C (39 : ℚ) := (map_ofNat C 39).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn40 : derivative ℚ (40 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 40
@[simp] lemma cc40 : constantCoeff (40 : PowerSeries ℚ) = 40 := by simpa using map_natCast (constantCoeff (R := ℚ)) 40
lemma cm40 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((40 : PowerSeries ℚ) * F) = 40 * coeff m F := by
  have e : (40 : PowerSeries ℚ) = C (40 : ℚ) := (map_ofNat C 40).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn42 : derivative ℚ (42 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 42
@[simp] lemma cc42 : constantCoeff (42 : PowerSeries ℚ) = 42 := by simpa using map_natCast (constantCoeff (R := ℚ)) 42
lemma cm42 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((42 : PowerSeries ℚ) * F) = 42 * coeff m F := by
  have e : (42 : PowerSeries ℚ) = C (42 : ℚ) := (map_ofNat C 42).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn46 : derivative ℚ (46 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 46
@[simp] lemma cc46 : constantCoeff (46 : PowerSeries ℚ) = 46 := by simpa using map_natCast (constantCoeff (R := ℚ)) 46
lemma cm46 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((46 : PowerSeries ℚ) * F) = 46 * coeff m F := by
  have e : (46 : PowerSeries ℚ) = C (46 : ℚ) := (map_ofNat C 46).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn55 : derivative ℚ (55 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 55
@[simp] lemma cc55 : constantCoeff (55 : PowerSeries ℚ) = 55 := by simpa using map_natCast (constantCoeff (R := ℚ)) 55
lemma cm55 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((55 : PowerSeries ℚ) * F) = 55 * coeff m F := by
  have e : (55 : PowerSeries ℚ) = C (55 : ℚ) := (map_ofNat C 55).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80 : derivative ℚ (80 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80
@[simp] lemma cc80 : constantCoeff (80 : PowerSeries ℚ) = 80 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80
lemma cm80 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80 : PowerSeries ℚ) * F) = 80 * coeff m F := by
  have e : (80 : PowerSeries ℚ) = C (80 : ℚ) := (map_ofNat C 80).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn90 : derivative ℚ (90 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 90
@[simp] lemma cc90 : constantCoeff (90 : PowerSeries ℚ) = 90 := by simpa using map_natCast (constantCoeff (R := ℚ)) 90
lemma cm90 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((90 : PowerSeries ℚ) * F) = 90 * coeff m F := by
  have e : (90 : PowerSeries ℚ) = C (90 : ℚ) := (map_ofNat C 90).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn102 : derivative ℚ (102 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 102
@[simp] lemma cc102 : constantCoeff (102 : PowerSeries ℚ) = 102 := by simpa using map_natCast (constantCoeff (R := ℚ)) 102
lemma cm102 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((102 : PowerSeries ℚ) * F) = 102 * coeff m F := by
  have e : (102 : PowerSeries ℚ) = C (102 : ℚ) := (map_ofNat C 102).symm
  rw [e, coeff_C_mul]

lemma S_sq : S * S = R := by
  have := bs_sq (R - 1) (by simp [R])
  unfold S; rw [this]; ring

noncomputable def DD : PowerSeries ℚ := 1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4
noncomputable def NN : PowerSeries ℚ := 1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S
noncomputable def AA : PowerSeries ℚ := NN * DD⁻¹

lemma hA : AA * DD = NN := by
  unfold AA
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [DD]), mul_one]

lemma hdD : derivative ℚ DD = 16*X^3 - 39*X^2 + 30*X - 7 := by
  simp [DD] <;> ring
lemma hdR : derivative ℚ R = -4 := by
  simp [R] <;> ring
lemma hdN : derivative ℚ NN = -80*X^4 + 32*X^3 - 27*X^2 + 20*X - 6 + (-6*X^5 + 10*X^4 - 6*X^2 + 2*X) * S + (-X^6 + 2*X^5 - 2*X^3 + X^2) * derivative ℚ S := by
  simp [NN] <;> ring

lemma ode : ((2) * X ^ 0 + (-11) * X ^ 1 + (14) * X ^ 2 + (14) * X ^ 3 + (-46) * X ^ 4 + (37) * X ^ 5 + (-10) * X ^ 6) * AA + ((-1) * X ^ 1 + (7) * X ^ 2 + (-14) * X ^ 3 + (6) * X ^ 4 + (11) * X ^ 5 + (-13) * X ^ 6 + (4) * X ^ 7) * derivative ℚ AA = ((2) * X ^ 0 + (-10) * X ^ 1 + (10) * X ^ 2 + (17) * X ^ 3 + (-40) * X ^ 4 + (55) * X ^ 5 + (14) * X ^ 6 + (24) * X ^ 7 : PowerSeries ℚ) := by
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
  linear_combination (832*X^11 - 5344*X^10 + 14228*X^9 - 19476*X^8 + 12444*X^7 + 1248*X^6 - 8580*X^5 + 6912*X^4 - 2844*X^3 + 656*X^2 - 80*X + 4) * r1 + (-128*X^12 + 864*X^11 - 2392*X^10 + 3282*X^9 - 1692*X^8 - 1428*X^7 + 3108*X^6 - 2448*X^5 + 1068*X^4 - 268*X^3 + 36*X^2 - 2*X) * r2 + (-16*X^17 + 136*X^16 - 481*X^15 + 856*X^14 - 586*X^13 - 608*X^12 + 1713*X^11 - 1488*X^10 + 228*X^9 + 712*X^8 - 751*X^7 + 376*X^6 - 106*X^5 + 16*X^4 - X^3) * r4

lemma ha (n : ℕ) : a n = coeff (n + 0) AA := rfl

lemma rec_a (k : ℕ) : (2 - ((k + 8 : ℕ) : ℚ)) * a (k + 8) + (7*((k + 8 : ℕ) : ℚ) - 18) * a (k + 7) + (42 - 14*((k + 8 : ℕ) : ℚ)) * a (k + 6) + (6*((k + 8 : ℕ) : ℚ) - 4) * a (k + 5) + (11*((k + 8 : ℕ) : ℚ) - 90) * a (k + 4) + (102 - 13*((k + 8 : ℕ) : ℚ)) * a (k + 3) + (4*((k + 8 : ℕ) : ℚ) - 34) * a (k + 2) = 0 := by
  have h := congrArg (coeff (k + 8)) ode
  simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm13, cm14, cm15, cm16, cm17, cm18, cm20, cm24, cm27, cm30, cm32, cm34, cm37, cm39, cm40, cm42, cm46, cm55, cm80, cm90, cm102, coeff_X_pow_mul', coeff_derivative] at h
  simp [PowerSeries.coeff_X] at h
  simp only [ha]
  simp only [Nat.add_assoc, Nat.reduceAdd] at h ⊢
  push_cast at h ⊢
  linear_combination h

end OMA.S_oeis_a274295

theorem OMA.solution : type_of% @OMA.S_oeis_a274295.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  simp only [show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 8 - 5 = k + 3 from by omega, show k + 8 - 6 = k + 2 from by omega]
  have h := OMA.S_oeis_a274295.rec_a k
  push_cast at h ⊢
  linear_combination h
