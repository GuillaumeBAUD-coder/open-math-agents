import OMAStatements.S_oeis_a230089
import Mathlib

/-!
Credit: @ivillar
Proof: (-1)^n, i^n and (-i)^n depend only on n mod 4, and the closed form is checked for each
residue. For the g.f., the denominator is (1-x^2)(1-x^4) = 1 - x^2 - x^4 + x^6, and
a(n) - a(n-2) - a(n-4) + a(n-6) = 0 for n ≥ 7 by a case split on n mod 4; the first seven
coefficients are checked directly.
-/

namespace OMAA230089Helpers
open PowerSeries OMA.S_oeis_a230089 Complex

theorem I_pow_four : I ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]
  norm_num

theorem pow_mod_four (z : ℂ) (hz : z ^ 4 = 1) (n : ℕ) : z ^ n = z ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, hz, one_pow, one_mul]

theorem closed (n : ℕ) (_hn : 1 ≤ n) : ((a n : ℤ) : ℂ) =
    (3 + 3 * (-1) ^ n + (-I) ^ n + I ^ n + n - (-1) ^ n * n) / 2 := by
  have h1 : (-1 : ℂ) ^ 4 = 1 := by norm_num
  have h2 : (-I) ^ 4 = 1 := by rw [neg_pow, I_pow_four]; norm_num
  rw [pow_mod_four (-1) h1 n, pow_mod_four (-I) h2 n, pow_mod_four I I_pow_four n]
  have hr : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hr with h | h | h | h
  · have ha : a n = 4 := by unfold a; rw [if_pos (by omega)]
    rw [ha, h]
    push_cast
    ring
  · have ha : a n = n := by unfold a; rw [if_neg (by omega), if_neg (by omega)]
    rw [ha, h]
    push_cast
    ring
  · have ha : a n = 2 := by unfold a; rw [if_neg (by omega), if_pos (by omega)]
    rw [ha, h]
    push_cast
    linear_combination (-1 : ℂ) * I_sq
  · have ha : a n = n := by unfold a; rw [if_neg (by omega), if_neg (by omega)]
    rw [ha, h]
    push_cast
    ring

def c (n : ℕ) : ℤ := if n = 0 then 0 else a n

theorem coeff_mk_mul_X_pow (n k : ℕ) :
    coeff n (PowerSeries.mk c * X ^ k) = if k ≤ n then c (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_at (n k j : ℕ) (h : n = j + k) : coeff n (PowerSeries.mk c * X ^ k) = c j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem rec_c (m : ℕ) : c (m + 7) - c (m + 5) - c (m + 3) + c (m + 1) = 0 := by
  simp only [c, a, show m + 7 ≠ 0 by omega, show m + 5 ≠ 0 by omega, show m + 3 ≠ 0 by omega,
    show m + 1 ≠ 0 by omega, ↓reduceIte]
  split_ifs <;> omega

end OMAA230089Helpers

open PowerSeries OMAA230089Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a230089.main := by
  refine ⟨closed, ?_⟩
  change PowerSeries.mk c * _ = _
  ext n
  have hD : ((X - 1) ^ 2 * (X + 1) ^ 2 * (X ^ 2 + 1) : PowerSeries ℤ) =
      X ^ 6 - X ^ 4 - X ^ 2 + X ^ 0 := by ring
  have hN : (-X * (4 * X ^ 5 - X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 - 2 * X - 1) : PowerSeries ℤ) =
      X ^ 5 + C 2 * X ^ 4 + C 2 * X ^ 3 + C 2 * X ^ 2 + X ^ 1 - C 4 * X ^ 6 := by
    rw [map_ofNat C 2, map_ofNat C 4]; ring
  rw [hD, hN]
  rcases Nat.lt_or_ge n 7 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_X_pow, coeff_C_mul, coeff_X_pow]
    interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at (m + 7) 6 (m + 1) (by omega), coeff_at (m + 7) 4 (m + 3) (by omega),
      coeff_at (m + 7) 2 (m + 5) (by omega), coeff_at (m + 7) 0 (m + 7) (by omega),
      coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow,
      coeff_X_pow, coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    linear_combination rec_c m
