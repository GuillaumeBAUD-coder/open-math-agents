import OMAStatements.S_oeis_a267186

/-!
# A267186: the conjectured package is inconsistent

The denominator `(1 - X) ^ 2 (1 + X + X ^ 2)` is `1 - X - X ^ 3 + X ^ 4`, so coefficient 6 of
the generating-function identity reads `a 6 - a 5 - a 3 + a 2 = -1`, while the claimed
recurrence at `n = 6` says that the same combination is `0`. So the conjunction of the claims is
false, whatever the sequence is.
-/

open OMA.S_oeis_a267186 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267186.main) := by
  rintro ⟨h, g⟩
  rw [show ∀ A : PowerSeries ℤ, A * ((1 - X) ^ 2 * (1 + X + X ^ 2)) =
    A - A * X ^ 1 - A * X ^ 3 + A * X ^ 4 by intro; ring, show (X * (2 + X - 3 * X ^ 2 +
    3 * X ^ 3 - X ^ 5 - X ^ 6) : PowerSeries ℤ) = C 2 * X ^ 1 + X ^ 2 - C 3 * X ^ 3 +
    C 3 * X ^ 4 - X ^ 6 - X ^ 7 by simp; ring] at g
  have := congrArg (coeff 6) g
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C] at this
  simp [coeff_X_pow] at this
  linarith [h 6 (by norm_num)]
