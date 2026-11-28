import OMAStatements.S_oeis_a289761
import Mathlib

-- Problem: A289761: Maximum length of a perfect Wichmann ruler with n segments.
-- Upstream: formal-conjectures statements/oeis-a289761.lean:0 (declaration OMA.S_oeis_a289761.main)
-- Credit: @nigelcarreiro-blip (the owner of the agent is credited as the solver)

/-! Proof idea: a(n + 6) = a(n) + 4 n + 18, because n + 6 and n have the same residue mod 6 and
(n + 6)^2 - n^2 = 3 (4 n + 12). The recurrence is the combination
[a(n) - a(n-6)] - 2 [a(n-1) - a(n-7)] + [a(n-2) - a(n-8)] = 0. The denominator of the g.f.
equals (1 - x)^2 (1 - x^6) = 1 - 2x + x^2 - x^6 + 2x^7 - x^8, so the coefficients of degree at
least 8 vanish by the recurrence and the first eight are checked directly. -/

namespace OMAA289761Helpers

open PowerSeries OMA.S_oeis_a289761

theorem a_add_six (k : ℕ) : a (k + 6) = a k + 4 * k + 18 := by
  unfold a
  push_cast
  have hm : ((k : ℤ) + 6) % 6 = (k : ℤ) % 6 := Int.add_emod_right _ _
  rw [hm, show ((k : ℤ) + 6) ^ 2 - ((k : ℤ) % 6 - 3) ^ 2
      = ((k : ℤ) ^ 2 - ((k : ℤ) % 6 - 3) ^ 2) + (4 * k + 12) * 3 by ring,
    Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

theorem recur (m : ℕ) :
    a (m + 8) = 2 * a (m + 7) - a (m + 6) + a (m + 2) - 2 * a (m + 1) + a m := by
  have h0 := a_add_six m
  have h1 := a_add_six (m + 1)
  have h2 := a_add_six (m + 2)
  rw [show m + 1 + 6 = m + 7 by omega] at h1
  rw [show m + 2 + 6 = m + 8 by omega] at h2
  push_cast at h0 h1 h2
  linarith

theorem coeff_mk_mul_X_pow (f : ℕ → ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem gf :
    PowerSeries.mk (fun n => (a (n + 2) : ℚ)) *
        ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2)) =
      (3 + 4 * X ^ 5 - 3 * X ^ 6 : PowerSeries ℚ) := by
  have hD : ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) =
      X ^ 0 - X ^ 1 - X ^ 1 + X ^ 2 - X ^ 6 + X ^ 7 + X ^ 7 - X ^ 8 := by
    ring
  have hN : (3 + 4 * X ^ 5 - 3 * X ^ 6 : PowerSeries ℚ) =
      X ^ 0 + X ^ 0 + X ^ 0 + X ^ 5 + X ^ 5 + X ^ 5 + X ^ 5 - X ^ 6 - X ^ 6 - X ^ 6 := by
    ring
  rw [hD, hN]
  ext n
  simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_X_pow, coeff_X_pow]
  rcases Nat.lt_or_ge n 8 with h | h
  · interval_cases n <;> norm_num [a]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have hr : a (m + 10) = 2 * a (m + 9) - a (m + 8) + a (m + 4) - 2 * a (m + 3) + a (m + 2) :=
      recur (m + 2)
    simp only [show 0 ≤ m + 8 by omega, show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega,
      show 6 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega, show 8 ≤ m + 8 by omega, ↓reduceIte,
      show m + 8 - 0 = m + 8 by omega, show m + 8 - 1 = m + 7 by omega,
      show m + 8 - 2 = m + 6 by omega, show m + 8 - 6 = m + 2 by omega,
      show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m by omega,
      show m + 8 ≠ 0 by omega, show m + 8 ≠ 5 by omega, show m + 8 ≠ 6 by omega,
      show m + 8 + 2 = m + 10 by omega, show m + 7 + 2 = m + 9 by omega,
      show m + 6 + 2 = m + 8 by omega, show m + 2 + 2 = m + 4 by omega,
      show m + 1 + 2 = m + 3 by omega]
    have hq : ((a (m + 10) : ℤ) : ℚ) = ((2 * a (m + 9) - a (m + 8) + a (m + 4)
        - 2 * a (m + 3) + a (m + 2) : ℤ) : ℚ) := by rw [hr]
    push_cast at hq
    linarith

end OMAA289761Helpers

open PowerSeries OMAA289761Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a289761.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
      show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega,
      show m + 10 - 8 = m + 2 by omega]
    exact recur (m + 2)
  · rw [mul_assoc, gf]
