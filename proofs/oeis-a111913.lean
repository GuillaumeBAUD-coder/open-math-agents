import OMAStatements.S_oeis_a111913
import Mathlib

/-!
Credit: @ivillar
Proof (as in Charles R Greathouse IV's remark in the OEIS entry): with
Q = (x^2+1)(x^4+1)(x^8+x^4+1) the denominator D satisfies D*Q = x^24 - 1. So the series G = N/D
satisfies G*(x^24 - 1) = N*Q, a polynomial of degree 23, whose coefficients beyond x^23 vanish;
comparing the coefficients of x^(n+24) gives a(n+24) = a(n).
-/

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a111913.main := by
  intro n
  set N : ℚ⟦X⟧ := X * (-2 - 3 * X - X ^ 2 + X ^ 7 + X ^ 8 + 2 * X ^ 4) with hN
  set D : ℚ⟦X⟧ := (X - 1) * (X + 1) * (X ^ 8 - X ^ 4 + 1) with hD
  set Q : ℚ⟦X⟧ := (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 8 + X ^ 4 + 1) with hQ
  have hD0 : constantCoeff D ≠ 0 := by
    rw [hD]
    simp
  have hDQ : D * Q = X ^ 24 - 1 := by
    rw [hD, hQ]
    ring
  have key : N * D⁻¹ * (X ^ 24 - 1) = N * Q := by
    rw [← hDQ, mul_assoc, ← mul_assoc D⁻¹ D Q, PowerSeries.inv_mul_cancel D hD0, one_mul]
  have hNQ : N * Q =
        -(C 2 * X ^ 1) - C 3 * X ^ 2 - C 3 * X ^ 3 - C 3 * X ^ 4 - C 3 * X ^ 5 - C 6 * X ^ 6 - C
        4 * X ^ 7 - C 5 * X ^ 8 - X ^ 9 - C 5 * X ^ 10 - X ^ 11 - C 4 * X ^ 12 + C 2 * X ^ 13 -
        X ^ 14 + C 3 * X ^ 15 - X ^ 16 + C 3 * X ^ 17 + C 2 * X ^ 18 + C 4 * X ^ 19 + X ^ 20 + X
        ^ 21 + X ^ 22 + X ^ 23 := by
    rw [hN, hQ, map_ofNat C 2, map_ofNat C 3, map_ofNat C 4, map_ofNat C 5, map_ofNat C 6]
    ring
  have hc := congrArg (coeff (n + 24)) key
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow, hNQ] at hc
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow] at hc
  show coeff (n + 24) (N * D⁻¹) = coeff n (N * D⁻¹)
  simp at hc
  linarith
