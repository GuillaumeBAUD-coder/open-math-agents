import OMAStatements.S_oeis_a186828
import Mathlib

namespace OMA.S_oeis_a186828

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
@[simp] lemma dn16 : derivative ℚ (16 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16
@[simp] lemma cc16 : constantCoeff (16 : PowerSeries ℚ) = 16 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16
lemma cm16 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16 : PowerSeries ℚ) * F) = 16 * coeff m F := by
  have e : (16 : PowerSeries ℚ) = C (16 : ℚ) := (map_ofNat C 16).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn26 : derivative ℚ (26 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 26
@[simp] lemma cc26 : constantCoeff (26 : PowerSeries ℚ) = 26 := by simpa using map_natCast (constantCoeff (R := ℚ)) 26
lemma cm26 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((26 : PowerSeries ℚ) * F) = 26 * coeff m F := by
  have e : (26 : PowerSeries ℚ) = C (26 : ℚ) := (map_ofNat C 26).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn33 : derivative ℚ (33 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 33
@[simp] lemma cc33 : constantCoeff (33 : PowerSeries ℚ) = 33 := by simpa using map_natCast (constantCoeff (R := ℚ)) 33
lemma cm33 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((33 : PowerSeries ℚ) * F) = 33 * coeff m F := by
  have e : (33 : PowerSeries ℚ) = C (33 : ℚ) := (map_ofNat C 33).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn38 : derivative ℚ (38 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 38
@[simp] lemma cc38 : constantCoeff (38 : PowerSeries ℚ) = 38 := by simpa using map_natCast (constantCoeff (R := ℚ)) 38
lemma cm38 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((38 : PowerSeries ℚ) * F) = 38 * coeff m F := by
  have e : (38 : PowerSeries ℚ) = C (38 : ℚ) := (map_ofNat C 38).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn49 : derivative ℚ (49 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 49
@[simp] lemma cc49 : constantCoeff (49 : PowerSeries ℚ) = 49 := by simpa using map_natCast (constantCoeff (R := ℚ)) 49
lemma cm49 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((49 : PowerSeries ℚ) * F) = 49 * coeff m F := by
  have e : (49 : PowerSeries ℚ) = C (49 : ℚ) := (map_ofNat C 49).symm
  rw [e, coeff_C_mul]

lemma S_sq : S * S = R := by
  have := bs_sq (R - 1) (by simp [R])
  unfold S; rw [this]; ring

noncomputable def DD : PowerSeries ℚ := 4 - 4 * X + 4 * X ^ 2 + 4 * X ^ 3
noncomputable def NN : PowerSeries ℚ := 1 + X - 3 * X ^ 2 + X ^ 3 + (-1 - X ^ 2) * S
noncomputable def AA : PowerSeries ℚ := NN * DD⁻¹

lemma hA : AA * DD = NN := by
  unfold AA
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [DD]), mul_one]

lemma hdD : derivative ℚ DD = 12*X^2 + 8*X - 4 := by
  simp [DD] <;> ring
lemma hdR : derivative ℚ R = 2*X - 6 := by
  simp [R] <;> ring
lemma hdN : derivative ℚ NN = 3*X^2 - 6*X + 1 + (-2*X) * S + (-X^2 - 1) * derivative ℚ S := by
  simp [NN] <;> ring

lemma ode : ((2) * X ^ 1 + (2) * X ^ 2 + (10) * X ^ 3 + (-26) * X ^ 4 + (8) * X ^ 5 + (-4) * X ^ 6) * AA + ((1) * X ^ 1 + (-7) * X ^ 2 + (9) * X ^ 3 + (-13) * X ^ 4 + (3) * X ^ 5 + (-5) * X ^ 6 + (-5) * X ^ 7 + (1) * X ^ 8) * derivative ℚ AA = ((1) * X ^ 1 + (-3) * X ^ 2 + (11) * X ^ 3 + (-3) * X ^ 4 + (-2) * X ^ 5 : PowerSeries ℚ) := by
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
  linear_combination (-24*X^12 + 216*X^11 - 216*X^10 - 1512*X^9 + 1104*X^8 + 240*X^7 - 2640*X^6 + 2640*X^5 - 1848*X^4 + 696*X^3 - 216*X^2 + 24*X) * r1 + (8*X^13 - 80*X^12 + 112*X^11 + 528*X^10 - 360*X^9 + 416*X^8 + 640*X^7 - 1184*X^6 + 1624*X^5 - 1104*X^4 + 528*X^3 - 112*X^2 + 8*X) * r2 + (-4*X^13 + 16*X^12 + 40*X^11 + 84*X^9 + 32*X^8 - 32*X^7 + 160*X^6 - 140*X^5 + 144*X^4 - 72*X^3 + 32*X^2 - 4*X) * r4

lemma ha (n : ℕ) : a n = coeff (n + 1) AA := rfl

lemma rec_a (k : ℕ) : (((k + 7 : ℕ) : ℚ) + 1) * a (k + 7) + (2 - 7*((k + 7 : ℕ) : ℚ)) * a (k + 6) + (9*((k + 7 : ℕ) : ℚ) - 7) * a (k + 5) + (36 - 13*((k + 7 : ℕ) : ℚ)) * a (k + 4) + (3*((k + 7 : ℕ) : ℚ) - 35) * a (k + 3) + (28 - 5*((k + 7 : ℕ) : ℚ)) * a (k + 2) + (21 - 5*((k + 7 : ℕ) : ℚ)) * a (k + 1) + (((k + 7 : ℕ) : ℚ) - 6) * a (k + 0) = 0 := by
  have h := congrArg (coeff (k + 8)) ode
  simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm13, cm16, cm26, cm33, cm38, cm49, coeff_X_pow_mul', coeff_derivative] at h
  simp [PowerSeries.coeff_X] at h
  simp only [ha]
  simp only [Nat.add_assoc, Nat.reduceAdd] at h ⊢
  push_cast at h ⊢
  linear_combination h

end OMA.S_oeis_a186828

theorem OMA.solution : type_of% @OMA.S_oeis_a186828.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 7 - 4 = k + 3 from by omega, show k + 7 - 5 = k + 2 from by omega, show k + 7 - 6 = k + 1 from by omega, show k + 7 - 7 = k + 0 from by omega]
  have h := OMA.S_oeis_a186828.rec_a k
  push_cast at h ⊢
  linear_combination h
