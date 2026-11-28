import OMAStatements.S_oeis_a298024

/-!
Credit: @unserus
Proof: G times the expanded denominator 1 - X - X^3 + X^4 is the numerator (the denominator is
invertible); comparing coefficient n > 4, where the numerator vanishes, gives the recurrence.
-/

namespace OMAA298024Helpers
open OMA.S_oeis_a298024 PowerSeries

theorem G_mul : G * (1 - X - X ^ 3 + X ^ 4) = 1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 := by
  have hD : ((1 - X) * (1 - X ^ 3) : PowerSeries ℚ) = 1 - X - X ^ 3 + X ^ 4 := by ring
  have h0 : constantCoeff ((1 - X) * (1 - X ^ 3) : PowerSeries ℚ) ≠ 0 := by simp
  unfold G
  rw [← hD, mul_assoc, PowerSeries.inv_mul_cancel _ h0, mul_one]

theorem coeff_G_mul (n : ℕ) (hn : 4 ≤ n) :
    coeff n (G * (1 - X - X ^ 3 + X ^ 4)) = a n - a (n - 1) - a (n - 3) + a (n - 4) := by
  rw [mul_add, mul_sub, mul_sub, mul_one, map_add, map_sub, map_sub, coeff_mul_X_pow',
    coeff_mul_X_pow', show G * X = G * X ^ 1 by rw [pow_one], coeff_mul_X_pow']
  simp only [if_pos (show 1 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos hn, a]

theorem coeff_N (n : ℕ) (hn : 4 < n) :
    coeff n (1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 : PowerSeries ℚ) = 0 := by
  have e : (1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 : PowerSeries ℚ) =
      C 1 * X ^ 0 + C 3 * X ^ 1 + C 6 * X ^ 2 + C 3 * X ^ 3 + C 1 * X ^ 4 := by
    have h3 : (C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat C 3
    have h6 : (C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat C 6
    rw [h3, h6, map_one]; ring
  rw [e]
  simp only [map_add, coeff_C_mul_X_pow]
  simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
    show n ≠ 4 by omega]

end OMAA298024Helpers

open OMAA298024Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a298024.main := by
  intro n hn
  have h := coeff_G_mul n (by omega)
  rw [G_mul, coeff_N n hn] at h
  linarith
