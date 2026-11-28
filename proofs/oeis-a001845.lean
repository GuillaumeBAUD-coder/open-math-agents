import OMAStatements.S_oeis_a001845
import Mathlib

/-!
Credit: @ivillar
Proof: the fourth difference of the cubic a(n) = (2n+1)(2n^2+2n+3)/3 vanishes, so (1-x)^4 times
the series is a polynomial of degree at most 3, whose coefficients are checked directly.
-/

namespace OMAA001845Helpers
open PowerSeries

theorem coeff_mk_mul_X_pow (f : ℕ → ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℚ) (r : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (f : ℕ → ℚ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (f : ℕ → ℚ) (r : ℚ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * f j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at f n k j h]

end OMAA001845Helpers

open PowerSeries OMAA001845Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a001845.main := by
  ext n
  have hD : ((1 - X) ^ 4 : PowerSeries ℚ) =
      X ^ 4 - C 4 * X ^ 3 + C 6 * X ^ 2 - C 4 * X ^ 1 + X ^ 0 := by
    rw [map_ofNat C 4, map_ofNat C 6]; ring
  have hN : ((1 + X) ^ 3 : PowerSeries ℚ) = X ^ 0 + C 3 * X ^ 1 + C 3 * X ^ 2 + X ^ 3 := by
    rw [map_ofNat C 3]; ring
  rw [hD, hN]
  rcases Nat.lt_or_ge n 4 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    interval_cases n <;> norm_num [OMA.S_oeis_a001845.a]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at _ (m + 4) 4 m (by omega), coeff_at_C _ 4 (m + 4) 3 (m + 1) (by omega),
      coeff_at_C _ 6 (m + 4) 2 (m + 2) (by omega), coeff_at_C _ 4 (m + 4) 1 (m + 3) (by omega),
      coeff_at _ (m + 4) 0 (m + 4) (by omega), coeff_C_mul, coeff_C_mul, coeff_X_pow,
      coeff_X_pow, coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    simp only [OMA.S_oeis_a001845.a]
    push_cast
    ring
