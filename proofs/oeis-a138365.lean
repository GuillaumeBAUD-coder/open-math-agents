import OMAStatements.S_oeis_a138365
import Mathlib

/-!
Credit: @ivillar
Proof idea (Sela Fried's remark in the OEIS entry): a(n+3) = 10*a(n+2) + 10*a(n+1) - a(n), which
follows by writing every term through b(n) and b(n+1); so the denominator
(x+1)*(x^2-11*x+1) = 1 - 10x - 10x^2 + x^3 annihilates the sequence from n = 3 on, and the
first coefficients are checked directly.
-/

namespace OMAA138365Helpers
open PowerSeries OMA.S_oeis_a138365

theorem b_succ_succ (n : ℕ) : b (n + 2) = 3 * b (n + 1) + b n := rfl

theorem a_rec (m : ℕ) : a (m + 3) = 10 * a (m + 2) + 10 * a (m + 1) - a m := by
  have h2 : b (m + 2) = 3 * b (m + 1) + b m := b_succ_succ m
  have h3 : b (m + 3) = 10 * b (m + 1) + 3 * b m := by
    rw [b_succ_succ (m + 1), h2]; ring
  have h4 : b (m + 4) = 33 * b (m + 1) + 10 * b m := by
    rw [b_succ_succ (m + 2), h3, h2]; ring
  have h5 : b (m + 5) = 109 * b (m + 1) + 33 * b m := by
    rw [b_succ_succ (m + 3), h4, h3]; ring
  unfold a
  rw [show m + 3 + 2 = m + 5 from rfl, show m + 2 + 2 = m + 4 from rfl,
    show m + 1 + 2 = m + 3 from rfl, h5, h4, h3, h2]
  ring

def c (n : ℕ) : ℤ := if n = 0 then 0 else a n

theorem c_eq (n : ℕ) : c n = a n := by
  unfold c
  split_ifs with h
  · subst h; rfl
  · rfl

theorem coeff_mk_mul_X_pow (n k : ℕ) :
    coeff n (PowerSeries.mk c * X ^ k) = if k ≤ n then c (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk c * (C r * X ^ k)) = r * (if k ≤ n then c (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (n k j : ℕ) (h : n = j + k) : coeff n (PowerSeries.mk c * X ^ k) = c j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk c * (C r * X ^ k)) = r * c j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at n k j h]

end OMAA138365Helpers

open PowerSeries OMAA138365Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a138365.main := by
  change PowerSeries.mk c * _ = _
  ext n
  have h10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have hD : ((X + 1) * (X ^ 2 - 11 * X + 1) : PowerSeries ℤ) =
      X ^ 3 - C 10 * X ^ 2 - C 10 * X ^ 1 + X ^ 0 := by
    rw [h10]; ring
  have hN : (-X * (X - 10) : PowerSeries ℤ) = C 10 * X ^ 1 - X ^ 2 := by
    rw [h10]; ring
  rw [hD, hN]
  rcases Nat.lt_or_ge n 3 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have hr := a_rec m
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at (m + 3) 3 m (by omega), coeff_at_C 10 (m + 3) 2 (m + 1) (by omega),
      coeff_at_C 10 (m + 3) 1 (m + 2) (by omega), coeff_at (m + 3) 0 (m + 3) (by omega),
      coeff_C_mul, coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega), c_eq, c_eq,
      c_eq, c_eq]
    linear_combination hr
