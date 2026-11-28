import OMAStatements.S_oeis_a080244
import Mathlib

namespace OMA.S_oeis_a080244

open PowerSeries

lemma hs : HasSubst (R - 1) := by
  apply HasSubst.of_constantCoeff_zero'
  simp [R]

lemma S_sq : S * S = R := by
  have h : PowerSeries.binomialSeries ℚ (1 / 2 + 1 / 2 : ℚ) = PowerSeries.binomialSeries ℚ (((1:ℕ):ℚ)) := by
    norm_num
  rw [PowerSeries.binomialSeries_add, PowerSeries.binomialSeries_nat] at h
  unfold S
  rw [← PowerSeries.subst_mul hs, h, pow_one, PowerSeries.subst_add hs, PowerSeries.subst_X hs]
  have h1 : PowerSeries.subst (R - 1) (1 : PowerSeries ℚ) = 1 := by
    have := PowerSeries.subst_C (S := ℚ) (a := R - 1) (1 : ℚ)
    simpa using this
  rw [h1]; ring

lemma S_c : constantCoeff S = 1 := by
  have h : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) =
      C (1:ℚ) + (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - C (1:ℚ)) := by ring
  have h0 : constantCoeff (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - C (1:ℚ)) = 0 := by
    simp
  have hc : PowerSeries.constantCoeff (R - 1) = 0 := by simp [R]
  have this : constantCoeff (PowerSeries.subst (R - 1) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - C (1:ℚ))) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (a := R - 1) hc _ h0
  unfold S
  rw [h, PowerSeries.subst_add hs, PowerSeries.subst_C, map_add, this]
  simp

lemma S_coeffs : coeff 1 S = 3 ∧ coeff 2 S = -4 ∧ coeff 3 S = 12 ∧ coeff 4 S = -44 ∧ coeff 5 S = 180 ∧ coeff 6 S = -788 := by
  have e0 : coeff 0 S = 1 := by simpa using S_c
  have hR : R = 1 + C (6:ℚ) * X + X ^ 2 := by
    unfold R; rw [map_ofNat C 6]
  have h : ∀ k, coeff k (S * S) = coeff k R := fun k => by rw [S_sq]
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  simp [coeff_mul, Finset.Nat.antidiagonal_succ, hR, coeff_C_mul, coeff_X_pow, coeff_X, e0] at h1 h2 h3 h4 h5 h6
  have s1 : coeff 1 S = 3 := by linarith
  have s2 : coeff 2 S = -4 := by rw [s1] at h2; linarith
  have s3 : coeff 3 S = 12 := by rw [s1, s2] at h3; linarith
  have s4 : coeff 4 S = -44 := by rw [s1, s2, s3] at h4; linarith
  have s5 : coeff 5 S = 180 := by rw [s1, s2, s3, s4] at h5; linarith
  have s6 : coeff 6 S = -788 := by rw [s1, s2, s3, s4, s5] at h6; linarith
  exact ⟨s1, s2, s3, s4, s5, s6⟩

lemma Dmul (T : PowerSeries ℚ) (k : ℕ) :
    coeff k ((2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) * T) =
      2 * coeff k T + 2 * (if 1 ≤ k then coeff (k - 1) T else 0)
        + 2 * (if 2 ≤ k then coeff (k - 2) T else 0) - 2 * (if 3 ≤ k then coeff (k - 3) T else 0) := by
  have : (2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) * T =
      C (2:ℚ) * (T + X ^ 1 * T + X ^ 2 * T - X ^ 3 * T) := by
    rw [map_ofNat C 2]; ring
  rw [this, coeff_C_mul]
  simp only [map_add, map_sub, coeff_X_pow_mul']
  ring

lemma a_vals : a 1 = 1 ∧ a 2 = -2 ∧ a 3 = 7 ∧ a 4 = -26 ∧ a 5 = 107 ∧ a 6 = -468 := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := S_coeffs
  have e0 : coeff 0 S = 1 := by simpa using S_c
  have hD : constantCoeff (2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
    have h2 : constantCoeff (2 : PowerSeries ℚ) = 2 := by rw [← map_ofNat C 2]; simp
    simp [h2]
  have hT : (2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) *
      ((-1 - X + 2 * X ^ 2 + S) * (2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹)
      = -1 - X + 2 * X ^ 2 + S := by
    rw [mul_comm (-1 - X + 2 * X ^ 2 + S), ← mul_assoc, PowerSeries.mul_inv_cancel _ hD, one_mul]
  have h : ∀ k, coeff k ((2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) *
      ((-1 - X + 2 * X ^ 2 + S) * (2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹))
      = coeff k (-1 - X + 2 * X ^ 2 + S) := fun k => by rw [hT]
  have c2 : ∀ k, coeff k (2 * X ^ 2 : PowerSeries ℚ) = if k = 2 then 2 else 0 := fun k => by
    rw [← map_ofNat C 2, coeff_C_mul, coeff_X_pow]; split_ifs <;> simp
  have hN : ∀ k, coeff k (-1 - X + 2 * X ^ 2 + S : PowerSeries ℚ) =
      (if k = 0 then -1 else 0) - (if k = 1 then 1 else 0) + (if k = 2 then 2 else 0) + coeff k S := by
    intro k
    simp only [map_add, map_sub, map_neg, c2, coeff_X, coeff_one]
    by_cases k0 : k = 0 <;> simp [k0]
  have hh : ∀ T : PowerSeries ℚ, (∀ k, coeff k ((2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) * T)
      = coeff k (-1 - X + 2 * X ^ 2 + S)) →
      coeff 1 T = 1 ∧ coeff 2 T = -2 ∧ coeff 3 T = 7 ∧ coeff 4 T = -26 ∧ coeff 5 T = 107 ∧ coeff 6 T = -468 := by
    intro T h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    simp only [Dmul, hN] at h0 h1 h2 h3 h4 h5 h6
    simp [e0, s1, s2, s3, s4, s5, s6] at h0 h1 h2 h3 h4 h5 h6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  exact hh _ h

end OMA.S_oeis_a080244

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a080244.main) := by
  intro H
  have h6 := H 6 le_rfl
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := OMA.S_oeis_a080244.a_vals
  norm_num at h6
  rw [a1, a2, a3, a4, a5, a6] at h6
  norm_num at h6
