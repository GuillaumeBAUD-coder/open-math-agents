import OMAStatements.S_oeis_a066999
import Mathlib

/-!
Credit: @ivillar
Proof: a(n+1) = 3*a(n) + (n+1)^3 (Peter Bala's recurrence in the OEIS entry), which gives
Vaclav Kotesovec's closed form a(n) = (11*3^(n+1) - 4n^3 - 18n^2 - 36n - 33)/8. The
denominator (3x-1)(x-1)^4 annihilates both the 3^n part and the cubic part from the 5th
coefficient on; the first five coefficients are checked directly.
-/

namespace OMAA066999Helpers
open PowerSeries OMA.S_oeis_a066999

def F (n : ℕ) : ℚ := (11 * 3 ^ (n + 1) - 4 * (n : ℚ) ^ 3 - 18 * (n : ℚ) ^ 2 - 36 * (n : ℚ) - 33) / 8

def G (k : ℕ) : ℚ := F (k + 1)

theorem a_succ (n : ℕ) : a (n + 1) = 3 * a n + ((n : ℚ) + 1) ^ 3 := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), pow_succ (3 : ℚ) n]
  push_cast
  field_simp

theorem a_eq (n : ℕ) : a n = F n := by
  induction n with
  | zero => norm_num [a, F]
  | succ n ih =>
    rw [a_succ, ih]
    unfold F
    push_cast
    ring

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

end OMAA066999Helpers

open PowerSeries OMAA066999Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a066999.main := by
  have hs : (fun k => OMA.S_oeis_a066999.a (k + 1)) = G := by
    funext k
    exact a_eq (k + 1)
  rw [hs]
  ext n
  have hD : ((3 * X - 1) * (X - 1) ^ 4 : PowerSeries ℚ) =
      C 3 * X ^ 5 - C 13 * X ^ 4 + C 22 * X ^ 3 - C 18 * X ^ 2 + C 7 * X ^ 1 - X ^ 0 := by
    rw [map_ofNat C 3, map_ofNat C 13, map_ofNat C 22, map_ofNat C 18, map_ofNat C 7]; ring
  have hN : (-1 - X ^ 2 - 4 * X : PowerSeries ℚ) = -X ^ 0 - X ^ 2 - C 4 * X ^ 1 := by
    rw [map_ofNat C 4]; ring
  rw [hD, hN]
  rcases Nat.lt_or_ge n 5 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, map_neg, coeff_mk_mul_C_X_pow,
      coeff_mk_mul_X_pow, coeff_C_mul, coeff_X_pow]
    interval_cases n <;> norm_num [G, F]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub, map_neg]
    rw [coeff_at_C G 3 (m + 5) 5 m (by omega), coeff_at_C G 13 (m + 5) 4 (m + 1) (by omega),
      coeff_at_C G 22 (m + 5) 3 (m + 2) (by omega), coeff_at_C G 18 (m + 5) 2 (m + 3) (by omega),
      coeff_at_C G 7 (m + 5) 1 (m + 4) (by omega), coeff_at G (m + 5) 0 (m + 5) (by omega),
      coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    unfold G F
    push_cast
    ring
