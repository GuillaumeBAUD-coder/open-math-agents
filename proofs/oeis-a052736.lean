import OMAStatements.S_oeis_a052736
import Mathlib

/-!
# OEIS A052736: the stated identity fails at the coefficient of `x`

Suppose `root` has constant term `1` and `root² = 1 - 6x + x²`. Comparing the coefficients of
`x` gives `2 [x] root = -6`, so `[x] root = -3`.

In the claimed identity `2x · royalSeries = 1 - 3x - root - x (1 - x - root)`:

* the coefficient of `x` on the left is `2 · royalSeries(0) = 2 · 1 = 2`;
* the coefficient of `x` on the right is `-3 - [x] root - (1 - 0 - 1) = -3 + 3 - 0 = 0`.

So no such `root` exists.
-/

open Finset PowerSeries OMA.S_oeis_a052736

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a052736.main) := by
  rintro ⟨root, h0, h2, h3⟩
  -- the coefficient of `x` in `root`
  have e1 := congrArg (coeff 1) h2
  rw [pow_two, coeff_one_mul, h0] at e1
  have hrhs : coeff 1 (1 - C (6 : ℚ) * X + X ^ 2 : ℚ⟦X⟧) = -6 := by
    simp [coeff_one, coeff_X_pow]
  rw [hrhs] at e1
  have r1 : coeff 1 root = -3 := by linarith
  -- the coefficient of `x` on both sides of the claimed identity
  have e2 := congrArg (coeff 1) h3
  have hL : coeff 1 (C (2 : ℚ) * X * royalSeries) = 2 := by
    rw [mul_assoc, coeff_C_mul, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]
    simp [royalSeries, largeSchroeder]
  have hR : coeff 1 (1 - C (3 : ℚ) * X - root - X * (1 - X - root)) = 0 := by
    rw [map_sub, map_sub, map_sub, coeff_C_mul, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]
    simp [coeff_one, coeff_X, h0, r1]
  rw [hL, hR] at e2
  norm_num at e2
