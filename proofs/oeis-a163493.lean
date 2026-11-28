import OMAStatements.S_oeis_a163493
import Mathlib

namespace OMA.S_oeis_a163493

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
@[simp] lemma dn12 : derivative ℚ (12 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 12
@[simp] lemma cc12 : constantCoeff (12 : PowerSeries ℚ) = 12 := by simpa using map_natCast (constantCoeff (R := ℚ)) 12
lemma cm12 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((12 : PowerSeries ℚ) * F) = 12 * coeff m F := by
  have e : (12 : PowerSeries ℚ) = C (12 : ℚ) := (map_ofNat C 12).symm
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
@[simp] lemma dn24 : derivative ℚ (24 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24
@[simp] lemma cc24 : constantCoeff (24 : PowerSeries ℚ) = 24 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24
lemma cm24 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24 : PowerSeries ℚ) * F) = 24 * coeff m F := by
  have e : (24 : PowerSeries ℚ) = C (24 : ℚ) := (map_ofNat C 24).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn32 : derivative ℚ (32 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32
@[simp] lemma cc32 : constantCoeff (32 : PowerSeries ℚ) = 32 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32
lemma cm32 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32 : PowerSeries ℚ) * F) = 32 * coeff m F := by
  have e : (32 : PowerSeries ℚ) = C (32 : ℚ) := (map_ofNat C 32).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn40 : derivative ℚ (40 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 40
@[simp] lemma cc40 : constantCoeff (40 : PowerSeries ℚ) = 40 := by simpa using map_natCast (constantCoeff (R := ℚ)) 40
lemma cm40 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((40 : PowerSeries ℚ) * F) = 40 * coeff m F := by
  have e : (40 : PowerSeries ℚ) = C (40 : ℚ) := (map_ofNat C 40).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn56 : derivative ℚ (56 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 56
@[simp] lemma cc56 : constantCoeff (56 : PowerSeries ℚ) = 56 := by simpa using map_natCast (constantCoeff (R := ℚ)) 56
lemma cm56 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((56 : PowerSeries ℚ) * F) = 56 * coeff m F := by
  have e : (56 : PowerSeries ℚ) = C (56 : ℚ) := (map_ofNat C 56).symm
  rw [e, coeff_C_mul]

lemma S_sq : S * S = R := by
  have := bs_sq (R - 1) (by simp [R])
  unfold S; rw [this]; ring

noncomputable def DD : PowerSeries ℚ := 2 - 4 * X + 2 * X ^ 2 - 8 * X ^ 3 + 8 * X ^ 4
noncomputable def NN : PowerSeries ℚ := 1 - X - 4 * X ^ 3 + (1 + 2 * X) * S
noncomputable def AA : PowerSeries ℚ := NN * DD⁻¹

lemma hA : AA * DD = NN := by
  unfold AA
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [DD]), mul_one]

lemma hdD : derivative ℚ DD = 32*X^3 - 24*X^2 + 4*X - 4 := by
  simp [DD] <;> ring
lemma hdR : derivative ℚ R = 16*X^3 - 12*X^2 + 2*X - 2 := by
  simp [R] <;> ring
lemma hdN : derivative ℚ NN = -12*X^2 - 1 + (2) * S + (2*X + 1) * derivative ℚ S := by
  simp [NN] <;> ring

lemma ode : ((3) * X ^ 1 + (-6) * X ^ 2 + (9) * X ^ 3 + (-10) * X ^ 4 + (-4) * X ^ 5 + (8) * X ^ 6) * AA + ((-1) * X ^ 1 + (1) * X ^ 2 + (3) * X ^ 3 + (-1) * X ^ 4 + (2) * X ^ 5 + (-12) * X ^ 6 + (8) * X ^ 7) * derivative ℚ AA = ((1) * X ^ 1 + (-2) * X ^ 2 + (4) * X ^ 3 : PowerSeries ℚ) := by
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
  linear_combination (-1536*X^14 + 5376*X^13 - 7552*X^12 + 7232*X^11 - 7584*X^10 + 6832*X^9 - 4296*X^8 + 2700*X^7 - 1752*X^6 + 764*X^5 - 280*X^4 + 132*X^3 - 40*X^2 + 4*X) * r1 + (512*X^15 - 1792*X^14 + 2432*X^13 - 2240*X^12 + 2464*X^11 - 2192*X^10 + 1160*X^9 - 676*X^8 + 428*X^7 - 52*X^6 - 52*X^5 + 20*X^4 - 28*X^3 + 20*X^2 - 4*X) * r2 + (128*X^12 - 256*X^11 + 96*X^10 - 32*X^9 + 120*X^8 - 54*X^6 - 10*X^5 - 4*X^4 + 12*X^3 + 2*X^2 - 2*X) * r4

lemma ha (n : ℕ) : a n = coeff (n + 0) AA := rfl

lemma rec_a (k : ℕ) : (-((k + 6 : ℕ) : ℚ)) * a (k + 6) + (((k + 6 : ℕ) : ℚ) + 2) * a (k + 5) + (3*((k + 6 : ℕ) : ℚ) - 12) * a (k + 4) + (12 - ((k + 6 : ℕ) : ℚ)) * a (k + 3) + (2*((k + 6 : ℕ) : ℚ) - 18) * a (k + 2) + (56 - 12*((k + 6 : ℕ) : ℚ)) * a (k + 1) + (8*((k + 6 : ℕ) : ℚ) - 40) * a (k + 0) = 0 := by
  have h := congrArg (coeff (k + 6)) ode
  rcases k with _ | k
  all_goals
    simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm12, cm16, cm18, cm24, cm32, cm40, cm56, coeff_X_pow_mul', coeff_derivative] at h
    simp [PowerSeries.coeff_X] at h
    simp only [ha]
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at h ⊢
    push_cast at h ⊢
    try simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
    linear_combination h

end OMA.S_oeis_a163493

theorem OMA.solution : type_of% @OMA.S_oeis_a163493.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 6 - 4 = k + 2 from by omega, show k + 6 - 5 = k + 1 from by omega, show k + 6 - 6 = k + 0 from by omega]
  have h := OMA.S_oeis_a163493.rec_a k
  push_cast at h ⊢
  linear_combination h
