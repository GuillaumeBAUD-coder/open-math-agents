import OMAStatements.S_mo_229028
import Mathlib

/-!
A disproof of the claim of MathOverflow question 229028 (see statements/mo-229028.lean).

The polynomial `p = 3 + 5 X + 3 X^2 + X^5` has the nonnegative coefficient sequence
`3, 5, 3, 0, 0, 1`, which is log-concave in the sense `a_{k-1} a_{k+1} ≤ a_k ^ 2`.  But `p` is not
a log-concave function on `[0, ∞)`: at `x = 1`, `y = 2`, `t = 1/2` one has

  p(1) = 12,  p(2) = 57,  p(3/2) = 795/32,  sqrt(p(1) p(2)) = sqrt(684) > 795/32 = p(3/2),

so `p(1)^(1/2) p(2)^(1/2) > p(3/2)` and the claimed inequality fails.
-/

open Polynomial

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_229028.main) := by
  intro h
  set p : ℝ[X] :=
    Polynomial.C (3 : ℝ) + Polynomial.C 5 * Polynomial.X +
      Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.X ^ 5 with hp
  have hdeg : p.natDegree = 5 := by
    rw [hp]
    compute_degree!
  have hz : ∀ k : ℕ, 6 ≤ k → p.coeff k = 0 := by
    intro k hk
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hnonneg : ∀ k : ℕ, 0 ≤ p.coeff k := by
    intro k
    by_cases hk : k ≤ 5
    · interval_cases k <;> simp [hp]
    · rw [hz k (by omega)]
  have hlog : ∀ k : ℕ, 1 ≤ k → p.coeff (k - 1) * p.coeff (k + 1) ≤ p.coeff k ^ 2 := by
    intro k hk
    by_cases hk6 : k ≤ 6
    · interval_cases k <;> simp [hp] <;> norm_num
    · have h1 : p.coeff (k - 1) = 0 := hz (k - 1) (by omega)
      have h2 : p.coeff (k + 1) = 0 := hz (k + 1) (by omega)
      have h3 : p.coeff k = 0 := hz k (by omega)
      rw [h1, h2, h3]
      norm_num
  have hres := h p hnonneg hlog 1 2 (by norm_num) (by norm_num) (1 / 2) (by norm_num)
    (by norm_num)
  have e1 : p.eval 1 = 12 := by
    rw [hp]
    simp
    norm_num
  have e2 : p.eval 2 = 57 := by
    rw [hp]
    simp
    norm_num
  have e3 : p.eval ((1 - (1 : ℝ) / 2) * 1 + (1 : ℝ) / 2 * 2) = 795 / 32 := by
    have hpt : (1 - (1 : ℝ) / 2) * 1 + (1 : ℝ) / 2 * 2 = 3 / 2 := by norm_num
    rw [hpt, hp]
    simp
    norm_num
  rw [e1, e2, e3] at hres
  have h12 : (12 : ℝ) ^ (1 - (1 : ℝ) / 2) = Real.sqrt 12 := by
    have hexp : 1 - (1 : ℝ) / 2 = 1 / 2 := by norm_num
    rw [hexp, ← Real.sqrt_eq_rpow]
  have h57 : (57 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 57 := by
    rw [← Real.sqrt_eq_rpow]
  have hmul : Real.sqrt 12 * Real.sqrt 57 = Real.sqrt 684 := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 12 by norm_num)]
    norm_num
  have hval : Real.sqrt 684 > 795 / 32 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 684 by norm_num), Real.sqrt_nonneg 684]
  rw [h12, h57, hmul] at hres
  linarith
