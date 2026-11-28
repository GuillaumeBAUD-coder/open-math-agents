import OMAStatements.S_mo_229028
import Mathlib

/-!
# MathOverflow 229028: a log-concave coefficient sequence does not give a log-concave function

Counterexample: `p = 1 + X ^ 3`.  Its coefficients `1, 0, 0, 1` are non-negative and satisfy
`c_{k-1} c_{k+1} ≤ c_k ^ 2` for every `k ≥ 1`, because the product on the left is always `0`
(the two non-zero coefficients are three apart, never two).  But with `x = 0`, `y = 2`,
`t = 1/2` the claimed inequality reads `p(0)^(1/2) · p(2)^(1/2) = 1 · 3 ≤ p(1) = 2`.
-/

open Polynomial in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_229028.main) := by
  intro h
  -- the coefficients of `1 + X ^ 3` are non-negative …
  have hc : ∀ k, 0 ≤ (1 + X ^ 3 : ℝ[X]).coeff k := by
    intro k
    simp only [coeff_add, coeff_one, coeff_X_pow]
    split_ifs <;> norm_num
  -- … and log-concave in the stated sense
  have hlc : ∀ k, 1 ≤ k →
      (1 + X ^ 3 : ℝ[X]).coeff (k - 1) * (1 + X ^ 3 : ℝ[X]).coeff (k + 1) ≤
        (1 + X ^ 3 : ℝ[X]).coeff k ^ 2 := by
    intro k hk
    simp only [coeff_add, coeff_one, coeff_X_pow]
    split_ifs <;> first | (exfalso; omega) | norm_num
  have key := h (1 + X ^ 3) hc hlc 0 2 le_rfl (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  have e0 : (1 + X ^ 3 : ℝ[X]).eval 0 = 1 := by simp
  have e2 : (1 + X ^ 3 : ℝ[X]).eval 2 = 9 := by norm_num
  have e1 : (1 + X ^ 3 : ℝ[X]).eval ((1 - 1 / 2) * 0 + 1 / 2 * 2) = 2 := by norm_num
  have h9 : (9 : ℝ) ^ ((1 : ℝ) / 2) = 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [e0, e2, e1, Real.one_rpow, h9] at key
  norm_num at key
