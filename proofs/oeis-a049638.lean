import OMAStatements.S_oeis_a049638
import Mathlib

-- Problem: A049638
-- Upstream: formal-conjectures statements/oeis-a049638.lean:0 (declaration OMA.S_oeis_a049638.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! Row m ≥ 2 of the gcd count has 1 + 2 [2 ∣ m] + [3 ∣ m] entries, and a(n+1) = a(n) + 5 - (row n+1).
The denominator is (1 - x^2)(1 - x^3) = 1 - x^2 - x^3 + x^5, and for n ≥ 6 the coefficient is
row(n-3) + row(n-4) - row(n) - row(n-1) = 0; the first six coefficients are computed directly. -/

namespace OMAA049638Helpers

open PowerSeries OMA.S_oeis_a049638

def row (m : ℕ) : ℤ := ∑ j ∈ Finset.range (4 + 1), if 1 < Nat.gcd m j then (1 : ℤ) else 0

theorem row_eq (m : ℕ) (hm : 2 ≤ m) :
    row m = 1 + (if m % 2 = 0 then 2 else 0) + (if m % 3 = 0 then 1 else 0) := by
  simp only [row, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [Nat.gcd_comm m 2, Nat.gcd_rec 2 m, Nat.gcd_comm m 3, Nat.gcd_rec 3 m, Nat.gcd_comm m 4,
    Nat.gcd_rec 4 m]
  simp only [Nat.gcd_zero_right, Nat.gcd_one_right, show 1 < m from hm, ↓reduceIte]
  rw [← Nat.mod_mod_of_dvd m (show 2 ∣ 12 by norm_num),
    ← Nat.mod_mod_of_dvd m (show 3 ∣ 12 by norm_num),
    ← Nat.mod_mod_of_dvd m (show 4 ∣ 12 by norm_num)]
  have : m % 12 < 12 := Nat.mod_lt _ (by norm_num)
  interval_cases m % 12 <;> decide

theorem a_succ (n : ℕ) : a (n + 1) = a n + 5 - row (n + 1) := by
  simp only [a, T, row, Finset.sum_range_succ _ (n + 1)]
  push_cast
  ring

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end OMAA049638Helpers

open PowerSeries OMA.S_oeis_a049638 OMAA049638Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a049638.main := by
  have hD : ((1 + X) * (1 + X + X ^ 2) * (X - 1) ^ 2 : PowerSeries ℚ) =
      C 1 * X ^ 0 - C 1 * X ^ 2 - C 1 * X ^ 3 + C 1 * X ^ 5 := by
    simp only [map_one]
    ring
  have hN : (2 * ((1 + X) * (1 + X + X ^ 2) * (X - 1) ^ 2) - X * (-7 - 9 * X - 5 * X ^ 2
      + 2 * X ^ 3 + 3 * X ^ 4) : PowerSeries ℚ) = C 2 * X ^ 0 + C 7 * X ^ 1 + C 7 * X ^ 2
      + C 3 * X ^ 3 - C 2 * X ^ 4 - C 1 * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hN, hD]
  ext n
  simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 6 with h | h
  · obtain ⟨v0, v1, v2, v3, v4, v5⟩ : a 0 = 2 ∧ a 1 = 7 ∧ a 2 = 9 ∧ a 3 = 12 ∧ a 4 = 14 ∧
        a 5 = 18 := by decide
    interval_cases n <;> simp [v0, v1, v2, v3, v4, v5] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have e1 : a (m + 6) = a (m + 5) + 5 - row (m + 6) := a_succ (m + 5)
    have e2 : a (m + 5) = a (m + 4) + 5 - row (m + 5) := a_succ (m + 4)
    have e3 : a (m + 3) = a (m + 2) + 5 - row (m + 3) := a_succ (m + 2)
    have e4 : a (m + 2) = a (m + 1) + 5 - row (m + 2) := a_succ (m + 1)
    have r1 := row_eq (m + 6) (by omega)
    have r2 := row_eq (m + 5) (by omega)
    have r3 := row_eq (m + 3) (by omega)
    have r4 := row_eq (m + 2) (by omega)
    have hz : a (m + 6) - a (m + 4) - a (m + 3) + a (m + 1) = 0 := by
      split_ifs at r1 r2 r3 r4 <;> omega
    have hq : ((a (m + 6) - a (m + 4) - a (m + 3) + a (m + 1) : ℤ) : ℚ) = 0 := by
      exact_mod_cast hz
    push_cast at hq
    simp only [show 0 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega,
      show 5 ≤ m + 6 by omega, ↓reduceIte, show m + 6 - 0 = m + 6 by omega,
      show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega,
      show m + 6 - 5 = m + 1 by omega, show m + 6 ≠ 0 by omega, show m + 6 ≠ 1 by omega,
      show m + 6 ≠ 2 by omega, show m + 6 ≠ 3 by omega, show m + 6 ≠ 4 by omega,
      show m + 6 ≠ 5 by omega]
    linarith
