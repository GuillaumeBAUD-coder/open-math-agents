import OMAStatements.S_oeis_a005313
import Mathlib

-- Problem: A005313
-- Upstream: formal-conjectures statements/oeis-a005313.lean:0 (declaration OMA.S_oeis_a005313.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! The denominator expands to 1 - 4x + 3x^2 + 3x^3 - 4x^4 + x^5. Writing a(m+5), ..., a(m) as a(m)
plus their last summands and every F(m+j) through F(m), F(m+1), the corresponding combination of
values is 0 by ring; the first five coefficients are computed directly. -/

namespace OMAA005313Helpers

open PowerSeries OMA.S_oeis_a005313

theorem rec5 (m : ℕ) :
    a (m + 5) = 4 * a (m + 4) - 3 * a (m + 3) - 3 * a (m + 2) + 4 * a (m + 1) - a m := by
  simp only [a, Finset.sum_range_succ, Nat.fib_add_two]
  push_cast
  ring

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end OMAA005313Helpers

open PowerSeries OMA.S_oeis_a005313 OMAA005313Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a005313.main := by
  have hD : ((1 - 3 * X + X ^ 2) * (1 + X) * (1 - X) ^ 2 : PowerSeries ℚ) = C 1 * X ^ 0
      - C 4 * X ^ 1 + C 3 * X ^ 2 + C 3 * X ^ 3 - C 4 * X ^ 4 + C 1 * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  have hN : (X * (1 - X - 3 * X ^ 2 + X ^ 3) : PowerSeries ℚ) =
      C 1 * X ^ 1 - C 1 * X ^ 2 - C 3 * X ^ 3 + C 1 * X ^ 4 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext n
  simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [a, Finset.sum_range_succ, Nat.fib_add_two] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have hq : ((a (m + 5) : ℤ) : ℚ) = ((4 * a (m + 4) - 3 * a (m + 3) - 3 * a (m + 2)
        + 4 * a (m + 1) - a m : ℤ) : ℚ) := by rw [rec5]
    push_cast at hq
    simp only [show 0 ≤ m + 5 by omega, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega,
      show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, ↓reduceIte,
      show m + 5 - 0 = m + 5 by omega, show m + 5 - 1 = m + 4 by omega,
      show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
      show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega,
      show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega,
      show m + 5 ≠ 4 by omega]
    linarith
