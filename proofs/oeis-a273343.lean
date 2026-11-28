import OMAStatements.S_oeis_a273343
import Mathlib

namespace OMA.S_oeis_a273343

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
@[simp] lemma dn9 : derivative ℚ (9 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9
@[simp] lemma cc9 : constantCoeff (9 : PowerSeries ℚ) = 9 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9
lemma cm9 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9 : PowerSeries ℚ) * F) = 9 * coeff m F := by
  have e : (9 : PowerSeries ℚ) = C (9 : ℚ) := (map_ofNat C 9).symm
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

lemma S_sq : S * S = R := by
  have := bs_sq (R - 1) (by simp [R])
  unfold S; rw [this]; ring

noncomputable def DD : PowerSeries ℚ := 2 - 2 * X
noncomputable def NN : PowerSeries ℚ := 1 - 3 * X + X ^ 3 + X ^ 4 + (-1 + X + X ^ 2) * S
noncomputable def AA : PowerSeries ℚ := NN * DD⁻¹

lemma hA : AA * DD = NN := by
  unfold AA
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [DD]), mul_one]

lemma hdD : derivative ℚ DD = -2 := by
  simp [DD] <;> ring
lemma hdR : derivative ℚ R = 4*X^3 + 4*X - 4 := by
  simp [R] <;> ring
lemma hdN : derivative ℚ NN = 4*X^3 + 3*X^2 - 3 + (2*X + 1) * S + (X^2 + X - 1) * derivative ℚ S := by
  simp [NN] <;> ring

lemma ode : ((2) * X ^ 1 + (-2) * X ^ 2 + (-7) * X ^ 3 + (1) * X ^ 4 + (1) * X ^ 5 + (3) * X ^ 6) * AA + ((1) * X ^ 1 + (-5) * X ^ 2 + (5) * X ^ 3 + (2) * X ^ 4 + (-1) * X ^ 5 + (-1) * X ^ 6 + (-1) * X ^ 7) * derivative ℚ AA = ((4) * X ^ 4 + (-3) * X ^ 5 + (3) * X ^ 6 : PowerSeries ℚ) := by
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
  linear_combination (-16*X^11 + 4*X^10 - 36*X^9 + 112*X^8 - 40*X^7 + 64*X^6 - 152*X^5 - 32*X^4 + 168*X^3 - 84*X^2 + 12*X) * r1 + (4*X^12 + 8*X^10 - 28*X^9 - 8*X^8 + 16*X^7 + 120*X^5 - 220*X^4 + 144*X^3 - 40*X^2 + 4*X) * r2 + (2*X^10 + 2*X^9 - 2*X^8 - 6*X^7 - 12*X^6 + 20*X^5 + 14*X^4 - 30*X^3 + 14*X^2 - 2*X) * r4

lemma ha (n : ℕ) : a n = coeff (n + 2) AA := rfl

lemma rec_a (k : ℕ) : (((k + 8 : ℕ) : ℚ) + 2) * a (k + 8) + (-5*((k + 8 : ℕ) : ℚ) - 3) * a (k + 7) + (5*((k + 8 : ℕ) : ℚ) - 2) * a (k + 6) + (2*((k + 8 : ℕ) : ℚ) - 9) * a (k + 5) + (3 - ((k + 8 : ℕ) : ℚ)) * a (k + 4) + (4 - ((k + 8 : ℕ) : ℚ)) * a (k + 3) + (7 - ((k + 8 : ℕ) : ℚ)) * a (k + 2) = 0 := by
  have h := congrArg (coeff (k + 10)) ode
  simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm9, cm12, cm13, coeff_X_pow_mul', coeff_derivative] at h
  simp [PowerSeries.coeff_X] at h
  simp only [ha]
  simp only [Nat.add_assoc, Nat.reduceAdd] at h ⊢
  push_cast at h ⊢
  linear_combination h

end OMA.S_oeis_a273343

theorem OMA.solution : type_of% @OMA.S_oeis_a273343.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  simp only [show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 8 - 5 = k + 3 from by omega, show k + 8 - 6 = k + 2 from by omega]
  have h := OMA.S_oeis_a273343.rec_a k
  push_cast at h ⊢
  linear_combination h
