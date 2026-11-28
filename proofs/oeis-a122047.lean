import OMAStatements.S_oeis_a122047
import Mathlib

-- Problem: A122047
-- Upstream: formal-conjectures statements/oeis-a122047.lean:0 (declaration OMA.S_oeis_a122047.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! The numerator grows by 15 (n+4)(n+5) = 30 T from n to n + 5, so a(n+5) = a(n) + T with
2 T = (n+4)(n+5). The third difference of this quadratic vanishes, which is the recurrence; the
g.f. denominator equals (1 - x)^3 (1 - x^5). -/

namespace OMAA122047Helpers

open PowerSeries OMA.S_oeis_a122047

theorem shift (n : ℕ) : 2 * (a (n + 5) - a n) = ((n : ℤ) + 4) * (n + 5) := by
  obtain ⟨T, hT⟩ := Int.even_mul_succ_self ((n : ℤ) + 4)
  have h : a (n + 5) = a n + T := by
    unfold a
    push_cast
    rw [show ((n : ℤ) + 5) ^ 3 + 6 * ((n : ℤ) + 5) ^ 2 + 5 * ((n : ℤ) + 5)
        = ((n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 5 * (n : ℤ)) + T * 30 by linear_combination 15 * hT,
      Int.add_mul_ediv_right _ _ (by norm_num)]
  rw [h]
  linear_combination -hT

theorem recur (m : ℕ) : a (m + 8) = 3 * a (m + 7) - 3 * a (m + 6) + a (m + 5) + a (m + 3)
    - 3 * a (m + 2) + 3 * a (m + 1) - a m := by
  apply mul_left_cancel₀ (two_ne_zero (α := ℤ))
  have s1 := shift (m + 1)
  have s2 := shift (m + 2)
  have s3 := shift (m + 3)
  push_cast at s1 s2 s3
  linear_combination s3 - 3 * s2 + 3 * s1 - shift m

theorem cX (f : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  split_ifs <;> simp

end OMAA122047Helpers

open PowerSeries OMA.S_oeis_a122047 OMAA122047Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a122047.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 5 = m + 3 by omega,
      show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega,
      show m + 8 - 8 = m by omega]
    exact recur m
  · have hD : ((1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 - X) ^ 4 : PowerSeries ℚ) = C 1 * X ^ 0
        - C 3 * X ^ 1 + C 3 * X ^ 2 - C 1 * X ^ 3 - C 1 * X ^ 5 + C 3 * X ^ 6 - C 3 * X ^ 7
        + C 1 * X ^ 8 := by
      simp only [map_one, map_ofNat]
      ring
    rw [mul_assoc, hD]
    ext n
    simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_X_pow]
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n <;> norm_num [a]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      have hq : ((a (m + 8) : ℤ) : ℚ) = ((3 * a (m + 7) - 3 * a (m + 6) + a (m + 5) + a (m + 3)
          - 3 * a (m + 2) + 3 * a (m + 1) - a m : ℤ) : ℚ) := by rw [recur]
      push_cast at hq
      simp only [show 0 ≤ m + 8 by omega, show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega,
        show 3 ≤ m + 8 by omega, show 5 ≤ m + 8 by omega, show 6 ≤ m + 8 by omega,
        show 7 ≤ m + 8 by omega, show 8 ≤ m + 8 by omega, ↓reduceIte,
        show m + 8 - 0 = m + 8 by omega, show m + 8 - 1 = m + 7 by omega,
        show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega,
        show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
        show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m by omega,
        show m + 8 ≠ 2 by omega]
      linarith
