import OMAStatements.S_oeis_a395454
import Mathlib

/-!
# A395454: the row-polynomial recurrence fails at `n = 2`

Compute the first rows of the triangle `T(n, k) = Σ_j (-1)^(n-j) C(n, j) E2(j, n - k)`, where
`E2` is the given second-order Eulerian triangle (`E2(0, ·) = 1, 0, 0, …`; `E2(1, ·) = 1, 0, …`;
`E2(2, ·) = 1, 2, 0, …`):

1. Row `1` is `T(1, 0) = 0`, `T(1, 1) = -1 + 1 = 0`, so the row polynomial `P₁ = 0`.
2. Row `2` is `T(2, 0) = 0`, `T(2, 1) = 2`, `T(2, 2) = 1 - 2 + 1 = 0`, so `P₂ = 2X`.
3. The claimed right-hand side at `n = 2` is
   `(…) · P₁ + (X - X²) · P₁' + X (2·2 - 4) · P₀ = 0`, because `P₁ = 0` and `2·2 - 4 = 0`.

So the recurrence would give `2X = 0`; comparing the coefficients of `X` refutes it.
-/

namespace OMA.S_oeis_a395454

open Polynomial

/-- Step 1: every entry of row `1` is `0`. -/
lemma triangle_one (k : ℕ) (hk : k ≤ 1) : triangle 1 k = 0 := by
  interval_cases k <;> decide

/-- Step 1: the first row polynomial vanishes. -/
lemma row_one : rowPolynomial 1 = 0 := by
  unfold rowPolynomial
  rw [Finset.sum_range_succ, Finset.sum_range_one, triangle_one 0 (by norm_num),
    triangle_one 1 le_rfl]
  simp

/-- Step 2: the coefficient of `X` in the second row polynomial is `T(2, 1) = 2`. -/
lemma row_two_coeff : (rowPolynomial 2).coeff 1 = 2 := by
  unfold rowPolynomial
  -- only the k = 1 term contributes, with value T(2, 1) = 2; T(2, 0) = T(2, 2) = 0
  have t0 : triangle 2 0 = 0 := by decide
  have t1 : triangle 2 1 = 2 := by decide
  have t2 : triangle 2 2 = 0 := by decide
  simp [Finset.sum_range_succ, t0, t1, t2]

/-- Step 3: the claimed right-hand side at `n = 2` is zero. -/
lemma rhs_two : recurrenceRHS 2 = 0 := by
  unfold recurrenceRHS
  rw [show 2 - 1 = 1 from rfl, row_one]
  -- the remaining term carries the factor 2·2 - 4 = 0
  simp only [mul_zero, derivative_zero, add_zero, zero_add]
  have h : (2 * ((2 : ℕ) : ℤ[X]) - 4) = 0 := by norm_num
  rw [h]
  simp

end OMA.S_oeis_a395454

open OMA.S_oeis_a395454 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a395454.main) := by
  intro h
  have h2 := congrArg (fun p => Polynomial.coeff p 1) (h 2 le_rfl)
  simp only [rhs_two, row_two_coeff, Polynomial.coeff_zero] at h2
  -- 2 = 0 is false
  norm_num at h2
