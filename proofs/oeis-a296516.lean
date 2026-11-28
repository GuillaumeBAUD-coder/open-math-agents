import OMAStatements.S_oeis_a296516
import Mathlib

-- Problem: A296516
-- Upstream: formal-conjectures statements/oeis-a296516.lean:0 (declaration OMA.S_oeis_a296516.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! For n >= 1, 2 a(n) = F(2n+1) + F(n+2) - n^2 + n - 2. The denominator
(1-x)^3 (1-3x+x^2) (1-x-x^2) = 1 - 7x + 18x^2 - 20x^3 + 6x^4 + 6x^5 - 5x^6 + x^7 annihilates each
part, so writing every Fibonacci value through F(2m), F(2m+1), F(m), F(m+1) the recurrence is an
identity checked by ring; the first eight coefficients are computed directly. -/

namespace OMAA296516Helpers

open PowerSeries OMA.S_oeis_a296516

theorem rec7 (m : ℕ) : a (m + 8) = 7 * a (m + 7) - 18 * a (m + 6) + 20 * a (m + 5)
    - 6 * a (m + 4) - 6 * a (m + 3) + 5 * a (m + 2) - a (m + 1) := by
  have hs : ∀ n, (Nat.fib (n + 4) : ℚ) = 3 * Nat.fib (n + 2) - Nat.fib n := fun n => by
    simp only [Nat.fib_add_two]
    push_cast
    ring
  have ht : ∀ n, (Nat.fib (n + 2) : ℚ) = Nat.fib (n + 1) + Nat.fib n := fun n => by
    rw [Nat.fib_add_two]
    push_cast
    ring
  simp only [a, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, ↓reduceIte]
  push_cast
  linear_combination (norm := ring_nf) (1 / 2 : ℚ) * (hs (2 * (m + 6) + 1) - 4 * hs (2 * (m + 5) + 1) + 5 * hs (2 * (m + 4) + 1) - hs (2 * (m + 3) + 1) - 2 * hs (2 * (m + 2) + 1) + hs (2 * (m + 1) + 1) + ht (m + 6 + 2) - 6 * ht (m + 5 + 2) + 13 * ht (m + 4 + 2) - 13 * ht (m + 3 + 2) + 6 * ht (m + 2 + 2) - ht (m + 1 + 2))

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end OMAA296516Helpers

open PowerSeries OMA.S_oeis_a296516 OMAA296516Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a296516.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hD : ((1 - X) ^ 3 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) : PowerSeries ℚ) = C 1 * X ^ 0
        - C 7 * X ^ 1 + C 18 * X ^ 2 - C 20 * X ^ 3 + C 6 * X ^ 4 + C 6 * X ^ 5 - C 5 * X ^ 6
        + C 1 * X ^ 7 := by
      simp only [map_one, map_ofNat]
      ring
    have hN : ((1 - X) ^ 3 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) +
        X * (1 - 5 * X + 9 * X ^ 2 - 5 * X ^ 3 - 2 * X ^ 4 + X ^ 5) : PowerSeries ℚ) =
        C 1 * X ^ 0 - C 6 * X ^ 1 + C 13 * X ^ 2 - C 11 * X ^ 3 + C 1 * X ^ 4 + C 4 * X ^ 5
        - C 4 * X ^ 6 + C 1 * X ^ 7 := by
      simp only [map_one, map_ofNat]
      ring
    rw [hN, hD]
    ext n
    simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n <;> norm_num [a, Nat.fib_add_two]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      have hr := rec7 m
      simp only [show 0 ≤ m + 8 by omega, show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega,
        show 3 ≤ m + 8 by omega, show 4 ≤ m + 8 by omega, show 5 ≤ m + 8 by omega,
        show 6 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega, ↓reduceIte,
        show m + 8 - 0 = m + 8 by omega, show m + 8 - 1 = m + 7 by omega,
        show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega,
        show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega,
        show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega,
        show m + 8 ≠ 0 by omega, show m + 8 ≠ 1 by omega, show m + 8 ≠ 2 by omega,
        show m + 8 ≠ 3 by omega, show m + 8 ≠ 4 by omega, show m + 8 ≠ 5 by omega,
        show m + 8 ≠ 6 by omega, show m + 8 ≠ 7 by omega]
      linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
      show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
      show m + 8 - 7 = m + 1 by omega]
    exact rec7 m
