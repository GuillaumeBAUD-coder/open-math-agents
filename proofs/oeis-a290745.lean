import OMAStatements.S_oeis_a290745
import Mathlib

-- Problem: A290745
-- Upstream: formal-conjectures statements/oeis-a290745.lean:0 (declaration OMA.S_oeis_a290745.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! a(n + 10) = a(n) + 9 n + 45, since n + 10 has the same residue and quotient + 1. The g.f.
denominator is (1 - x)^2 (1 - x^10), so coefficients of degree at least 13 vanish by the second
difference of a(n) - a(n - 10); the first thirteen are computed directly. -/

namespace OMAA290745Helpers

open PowerSeries OMA.S_oeis_a290745

theorem c2 (n : ℕ) : 2 * (n.choose 2 : ℤ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem shift (n : ℕ) : a (n + 10) = a n + 9 * n + 45 := by
  have hn : (n : ℤ) = 10 * ((n / 10 : ℕ) : ℤ) + ((n % 10 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod n 10).symm
  have h1 := c2 (n + 10 + 1)
  have h2 := c2 (n + 1)
  have h3 := c2 (n / 10 + 1 + 1)
  have h4 := c2 (n / 10 + 1)
  have h5 := c2 (n / 10 + 1 + 2)
  apply mul_left_cancel₀ (two_ne_zero (α := ℤ))
  simp only [a, Nat.add_mod_right, Nat.add_div_right n (show 0 < 10 by norm_num)]
  rw [show n / 10 + 2 = n / 10 + 1 + 1 by omega]
  push_cast at h1 h2 h3 h4 h5 hn ⊢
  linear_combination h1 - h2 - (10 - (n : ℤ) % 10) * (h3 - h4)
    - ((n : ℤ) % 10) * (h5 - h3) + 2 * hn

theorem recur (m : ℕ) : a (m + 12) = 2 * a (m + 11) - a (m + 10) + a (m + 2) - 2 * a (m + 1)
    + a m := by
  have h0 := shift m
  have h1 := shift (m + 1)
  have h2 := shift (m + 2)
  push_cast at h0 h1 h2
  linarith

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end OMAA290745Helpers

open PowerSeries OMA.S_oeis_a290745 OMAA290745Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a290745.main := by
  have hD : ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2 - X ^ 3 + X ^ 4) *
      (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℚ) = C 1 * X ^ 0 - C 2 * X ^ 1
      + C 1 * X ^ 2 - C 1 * X ^ 10 + C 2 * X ^ 11 - C 1 * X ^ 12 := by
    simp only [map_one, map_ofNat]
    ring
  have hN : (X * (10 - 9 * X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9
      - 10 * X ^ 10 + 10 * X ^ 11) : PowerSeries ℚ) = C 10 * X ^ 1 - C 9 * X ^ 2 + C 1 * X ^ 3
      + C 1 * X ^ 4 + C 1 * X ^ 5 + C 1 * X ^ 6 + C 1 * X ^ 7 + C 1 * X ^ 8 + C 1 * X ^ 9
      + C 1 * X ^ 10 - C 10 * X ^ 11 + C 10 * X ^ 12 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext n
  simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;> norm_num [b, a, Nat.choose]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
    have hb : ∀ k, b (k + 1) = a (k + 1) := fun k => by simp [b]
    have hr : a (m + 12 + 1) = 2 * a (m + 11 + 1) - a (m + 10 + 1) + a (m + 2 + 1)
        - 2 * a (m + 1 + 1) + a (m + 1) := recur (m + 1)
    simp only [show 0 ≤ m + 13 by omega, show 1 ≤ m + 13 by omega, show 2 ≤ m + 13 by omega,
      show 10 ≤ m + 13 by omega, show 11 ≤ m + 13 by omega, show 12 ≤ m + 13 by omega,
      ↓reduceIte, show m + 13 - 0 = m + 12 + 1 by omega, show m + 13 - 1 = m + 11 + 1 by omega,
      show m + 13 - 2 = m + 10 + 1 by omega, show m + 13 - 10 = m + 2 + 1 by omega,
      show m + 13 - 11 = m + 1 + 1 by omega, show m + 13 - 12 = m + 1 by omega,
      show m + 13 ≠ 1 by omega, show m + 13 ≠ 2 by omega, show m + 13 ≠ 3 by omega,
      show m + 13 ≠ 4 by omega, show m + 13 ≠ 5 by omega, show m + 13 ≠ 6 by omega,
      show m + 13 ≠ 7 by omega, show m + 13 ≠ 8 by omega, show m + 13 ≠ 9 by omega,
      show m + 13 ≠ 10 by omega, show m + 13 ≠ 11 by omega, show m + 13 ≠ 12 by omega, hb]
    have hq : ((a (m + 12 + 1) : ℤ) : ℚ) = ((2 * a (m + 11 + 1) - a (m + 10 + 1)
        + a (m + 2 + 1) - 2 * a (m + 1 + 1) + a (m + 1) : ℤ) : ℚ) := by rw [hr]
    push_cast at hq
    linarith
