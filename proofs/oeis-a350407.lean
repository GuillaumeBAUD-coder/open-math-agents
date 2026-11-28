import OMAStatements.S_oeis_a350407
import Mathlib

/-!
# A350407: the supercongruence fails for `p = 5`, `n = 1`, `r = 1`

Let `P = 1 + X + X² + X³ + X⁴`, so `g P = 1` and `g⁵ P⁵ = 1`.  Comparing coefficients of
`X⁰, …, X⁵` in `g⁵ P⁵ = 1` gives the first coefficients of `g⁵`:
`1, -5, 10, -10, 5, 4`; in particular `a 5 = 4`.  Likewise `g P = 1` gives `a 1 = -1`.
But `4 - (-1) = 5` is not divisible by `5² = 25`.
-/

namespace OMA.S_oeis_a350407

open PowerSeries

lemma g_mul : g * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) = 1 := by
  rw [mul_comm]
  exact PowerSeries.mul_invOfUnit _ 1 (by simp)

lemma a_one : a 1 = -1 := by
  have el : ∀ S : PowerSeries ℤ, S * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) =
      S * X ^ 0 + S * X ^ 1 + S * X ^ 2 + S * X ^ 3 + S * X ^ 4 := by
    intro S
    ring
  have h := g_mul
  rw [el] at h
  have h0 := congrArg (coeff 0) h
  have h1 := congrArg (coeff 1) h
  simp only [map_add, coeff_mul_X_pow'] at h0 h1
  simp at h0 h1
  unfold a
  rw [pow_one]
  linarith

lemma a_five : a 5 = 4 := by
  have hS : g ^ 5 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) ^ 5 = 1 := by
    rw [← mul_pow, g_mul, one_pow]
  have el : ∀ S : PowerSeries ℤ, S * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) ^ 5 =
      C (1 : ℤ) * (S * X ^ 0) + C (5 : ℤ) * (S * X ^ 1) + C (15 : ℤ) * (S * X ^ 2) + C (35 : ℤ) * (S * X ^ 3) + C (70 : ℤ) * (S * X ^ 4) + C (121 : ℤ) * (S * X ^ 5) + C (185 : ℤ) * (S * X ^ 6) + C (255 : ℤ) * (S * X ^ 7) + C (320 : ℤ) * (S * X ^ 8) + C (365 : ℤ) * (S * X ^ 9) + C (381 : ℤ) * (S * X ^ 10) + C (365 : ℤ) * (S * X ^ 11) + C (320 : ℤ) * (S * X ^ 12) + C (255 : ℤ) * (S * X ^ 13) + C (185 : ℤ) * (S * X ^ 14) + C (121 : ℤ) * (S * X ^ 15) + C (70 : ℤ) * (S * X ^ 16) + C (35 : ℤ) * (S * X ^ 17) + C (15 : ℤ) * (S * X ^ 18) + C (5 : ℤ) * (S * X ^ 19) + C (1 : ℤ) * (S * X ^ 20) := by
    intro S
    simp only [map_one, map_ofNat]
    ring
  rw [el] at hS
  unfold a
  generalize g ^ 5 = S at hS ⊢
  have v0 : coeff 0 S = 1 := by
    have h := congrArg (coeff 0) hS
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow'] at h
    simp [-PowerSeries.coeff_zero_eq_constantCoeff] at h
    linarith
  have v1 : coeff 1 S = -5 := by
    have h := congrArg (coeff 1) hS
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow'] at h
    simp [-PowerSeries.coeff_zero_eq_constantCoeff, v0] at h
    linarith
  have v2 : coeff 2 S = 10 := by
    have h := congrArg (coeff 2) hS
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow'] at h
    simp [-PowerSeries.coeff_zero_eq_constantCoeff, v0, v1] at h
    linarith
  have v3 : coeff 3 S = -10 := by
    have h := congrArg (coeff 3) hS
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow'] at h
    simp [-PowerSeries.coeff_zero_eq_constantCoeff, v0, v1, v2] at h
    linarith
  have v4 : coeff 4 S = 5 := by
    have h := congrArg (coeff 4) hS
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow'] at h
    simp [-PowerSeries.coeff_zero_eq_constantCoeff, v0, v1, v2, v3] at h
    linarith
  have v5 : coeff 5 S = 4 := by
    have h := congrArg (coeff 5) hS
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow'] at h
    simp [-PowerSeries.coeff_zero_eq_constantCoeff, v0, v1, v2, v3, v4] at h
    linarith
  exact v5

end OMA.S_oeis_a350407

open OMA.S_oeis_a350407 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a350407.main) := by
  intro h
  have h5 := h 1 1 5 le_rfl le_rfl (by norm_num) (by norm_num)
  have e1 : 1 * 5 ^ 1 = 5 := by norm_num
  have e2 : 1 * 5 ^ (1 - 1) = 1 := by norm_num
  rw [e1, e2, a_five, a_one] at h5
  revert h5
  decide
