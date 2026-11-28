import OMAStatements.S_oeis_a335756
import Mathlib

-- Problem: A335756
-- Upstream: formal-conjectures statements/oeis-a335756.lean:0 (declaration OMA.S_oeis_a335756.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! n, n + 3 and n + 6 have the same residue mod 3, and on each residue class a is affine in n, so
a(n+6) - 2 a(n+3) + a(n) = 0. The g.f. denominator equals (1 - x^3)^2 = 1 - 2x^3 + x^6. -/

namespace OMAA335756Helpers

open PowerSeries OMA.S_oeis_a335756

theorem recur (n : ℕ) : a (n + 6) = 2 * a (n + 3) - a n := by
  simp only [a, show (n + 6) % 3 = n % 3 by omega, show (n + 3) % 3 = n % 3 by omega,
    show (n + 6) / 3 = n / 3 + 2 by omega, show (n + 3) / 3 = n / 3 + 1 by omega]
  split_ifs <;> push_cast <;> ring

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end OMAA335756Helpers

open PowerSeries OMA.S_oeis_a335756 OMAA335756Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a335756.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hD : ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 : PowerSeries ℚ) =
        C 1 * X ^ 0 - C 2 * X ^ 3 + C 1 * X ^ 6 := by
      simp only [map_one, map_ofNat]
      ring
    have hN : (2 * (1 + X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5) : PowerSeries ℚ) =
        C 2 * X ^ 0 + C 2 * X ^ 2 + C 8 * X ^ 3 + C 6 * X ^ 4 + C 4 * X ^ 5 := by
      simp only [map_ofNat]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> norm_num [a]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have hq : ((a (m + 6) : ℤ) : ℚ) = ((2 * a (m + 3) - a m : ℤ) : ℚ) := by rw [recur]
      push_cast at hq
      simp only [show 0 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 6 ≤ m + 6 by omega,
        ↓reduceIte, show m + 6 - 0 = m + 6 by omega, show m + 6 - 3 = m + 3 by omega,
        show m + 6 - 6 = m by omega, show m + 6 ≠ 0 by omega, show m + 6 ≠ 2 by omega,
        show m + 6 ≠ 3 by omega, show m + 6 ≠ 4 by omega, show m + 6 ≠ 5 by omega]
      linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 3 = m + 3 by omega, show m + 6 - 6 = m by omega]
    exact recur m
