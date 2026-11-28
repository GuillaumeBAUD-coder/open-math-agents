import OMAStatements.S_mo_437635
import Mathlib

/-!
# MathOverflow 437635: the statement fails for `q = 5`

The primes below `5` are `2` and `3`. If `x² + p y² = 5` then `x² ≤ 5` and `y² ≤ 2`, so
`|x| ≤ 2` and `|y| ≤ 1`; none of the finitely many cases gives `5`
(`x² + 2y² ∈ {0, 1, 2, 3, 4, 6}` and `x² + 3y² ∈ {0, 1, 3, 4, 7}`).
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_437635.main) := by
  intro h
  obtain ⟨p, x, y, hp, hpq, hxy⟩ := h 5 (by norm_num) (by decide) (by norm_num)
  have hp2 := hp.two_le
  have hxx : 0 ≤ x ^ 2 := sq_nonneg x
  have hyy : 0 ≤ y ^ 2 := sq_nonneg y
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp2
  have hxy' : x ^ 2 + (p : ℤ) * y ^ 2 = 5 := by exact_mod_cast hxy
  have hpy : 0 ≤ (p : ℤ) * y ^ 2 := mul_nonneg (by linarith) hyy
  have hpy2 : 2 * y ^ 2 ≤ (p : ℤ) * y ^ 2 := mul_le_mul_of_nonneg_right hpZ hyy
  have hx1 : x ^ 2 ≤ 5 := by linarith
  have hy1 : y ^ 2 ≤ 2 := by linarith
  have hx : -2 ≤ x ∧ x ≤ 2 := by constructor <;> nlinarith
  have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith
  obtain ⟨hxl, hxu⟩ := hx
  obtain ⟨hyl, hyu⟩ := hy
  interval_cases p
  · interval_cases x <;> interval_cases y <;> norm_num at hxy'
  · interval_cases x <;> interval_cases y <;> norm_num at hxy'
  · exact absurd hp (by decide)
