import OMAStatements.S_oeis_a290744
import Mathlib

-- Problem: A290744
-- Upstream: formal-conjectures statements/oeis-a290744.lean:0 (declaration OMA.S_oeis_a290744.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! Proof idea: a(n + 5) = a(n) + 4 n + 10, since n + 5 has the same residue r and quotient q + 1.
The recurrence is [a(n) - a(n-5)] - 2 [a(n-1) - a(n-6)] + [a(n-2) - a(n-7)] = 0, and the
denominator of the g.f. is (1 - x)^2 (1 - x^5) = 1 - 2x + x^2 - x^5 + 2x^6 - x^7. -/

namespace OMAA290744Helpers

open PowerSeries OMA.S_oeis_a290744

theorem c2 (n : ℕ) : 2 * (n.choose 2 : ℤ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem shift (n : ℕ) : a (n + 5) = a n + 4 * n + 10 := by
  have hn : (n : ℤ) = 5 * ((n / 5 : ℕ) : ℤ) + ((n % 5 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod n 5).symm
  have h1 := c2 (n + 5 + 1)
  have h2 := c2 (n + 1)
  have h3 := c2 (n / 5 + 1 + 1)
  have h4 := c2 (n / 5 + 1)
  have h5 := c2 (n / 5 + 1 + 2)
  apply mul_left_cancel₀ (two_ne_zero (α := ℤ))
  simp only [a, Nat.add_mod_right, Nat.add_div_right n (show 0 < 5 by norm_num)]
  rw [show n / 5 + 2 = n / 5 + 1 + 1 by omega]
  push_cast at h1 h2 h3 h4 h5 hn ⊢
  linear_combination h1 - h2 - (5 - (n : ℤ) % 5) * (h3 - h4)
    - ((n : ℤ) % 5) * (h5 - h3) + 2 * hn

theorem recur (m : ℕ) :
    a (m + 7) = 2 * a (m + 6) - a (m + 5) + a (m + 2) - 2 * a (m + 1) + a m := by
  have h0 := shift m
  have h1 := shift (m + 1)
  have h2 := shift (m + 2)
  push_cast at h0 h1 h2
  linarith

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end OMAA290744Helpers

open PowerSeries OMA.S_oeis_a290744 OMAA290744Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a290744.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hD : ((1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℚ) =
        C 1 * X ^ 0 - C 2 * X ^ 1 + C 1 * X ^ 2 - C 1 * X ^ 5 + C 2 * X ^ 6 - C 1 * X ^ 7 := by
      simp only [map_one, map_ofNat]
      ring
    have hN : (X * (5 - 4 * X + X ^ 2 + X ^ 3 + X ^ 4 - 5 * X ^ 5 + 5 * X ^ 6) : PowerSeries ℚ) =
        C 5 * X ^ 1 - C 4 * X ^ 2 + C 1 * X ^ 3 + C 1 * X ^ 4 + C 1 * X ^ 5 - C 5 * X ^ 6
          + C 5 * X ^ 7 := by
      simp only [map_one, map_ofNat]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n <;> norm_num [b, a, Nat.choose]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      have hb : ∀ k, b (k + 1) = a (k + 1) := fun k => by simp [b]
      have hr : a (m + 7 + 1) = 2 * a (m + 6 + 1) - a (m + 5 + 1) + a (m + 2 + 1)
          - 2 * a (m + 1 + 1) + a (m + 1) := recur (m + 1)
      simp only [show 0 ≤ m + 8 by omega, show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega,
        show 5 ≤ m + 8 by omega, show 6 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega, ↓reduceIte,
        show m + 8 - 0 = m + 7 + 1 by omega, show m + 8 - 1 = m + 6 + 1 by omega,
        show m + 8 - 2 = m + 5 + 1 by omega, show m + 8 - 5 = m + 2 + 1 by omega,
        show m + 8 - 6 = m + 1 + 1 by omega, show m + 8 - 7 = m + 1 by omega,
        show m + 8 ≠ 1 by omega, show m + 8 ≠ 2 by omega, show m + 8 ≠ 3 by omega,
        show m + 8 ≠ 4 by omega, show m + 8 ≠ 5 by omega, show m + 8 ≠ 6 by omega,
        show m + 8 ≠ 7 by omega, hb]
      have hq : ((a (m + 7 + 1) : ℤ) : ℚ) = ((2 * a (m + 6 + 1) - a (m + 5 + 1) + a (m + 2 + 1)
          - 2 * a (m + 1 + 1) + a (m + 1) : ℤ) : ℚ) := by rw [hr]
      push_cast at hq
      linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
      show m + 7 - 7 = m by omega]
    exact recur m
